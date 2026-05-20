use crate::{Map, Result};
use std::{
    any::{self, Any, TypeId},
    borrow::Cow,
    ops::Deref,
};

/// Parses `code` as `T` and returns a syntax tree bundled with its locations.
///
/// This is the easiest entry point. The returned [`Located`] owns the parsed syntax tree and the
/// [`Locator`] that stores locations for its nodes.
///
/// # Examples
///
/// ```rust
/// use syn_locator::Location;
///
/// let code = "struct Foo { value: i32 }";
/// let located = syn_locator::locate::<syn::File>("file.rs", code).unwrap();
///
/// let syn::Item::Struct(item_struct) = &located.items[0] else {
///     unreachable!()
/// };
/// let field_ty = &item_struct.fields.iter().next().unwrap().ty;
///
/// assert_eq!(located.code(field_ty), "i32");
/// assert!(matches!(located.location(field_ty), Location { start: 20, end: 23, .. }));
/// ```
pub fn locate<T>(file_path: &str, code: &str) -> Result<Located<T>>
where
    T: syn::parse::Parse + Locate,
{
    Located::new(syn::parse_str::<T>(code)?, file_path, code)
}

/// A parsed syntax tree bundled with the locator that belongs to it.
///
/// `Located<T>` keeps the syntax tree on the heap, so moving the wrapper does not move the syntax
/// nodes whose addresses are used by the internal [`Locator`]. It dereferences to `T` for
/// convenient access to the syntax tree.
pub struct Located<T: Locate> {
    syntax: Box<T>,
    locator: Locator,
}

impl<T: Locate> Located<T> {
    /// Creates a located wrapper from an already parsed syntax tree.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use syn_locator::Located;
    ///
    /// let code = "fn foo() {}";
    /// let syntax = syn::parse_str::<syn::ItemFn>(code).unwrap();
    /// let located = Located::new(syntax, "file.rs", code).unwrap();
    ///
    /// assert_eq!(located.code(&located.sig.ident), "foo");
    /// ```
    pub fn new(syntax: T, file_path: &str, code: impl Into<Box<str>>) -> Result<Self> {
        let syntax = Box::new(syntax);
        let mut locator = Locator::new(file_path, code);
        syntax.locate_as_entry(&mut locator)?;
        Ok(Self { syntax, locator })
    }

    /// Returns the located syntax tree.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use syn_locator::Locate;
    ///
    /// let located = syn_locator::locate::<syn::ItemStruct>("file.rs", "struct Foo;").unwrap();
    ///
    /// assert_eq!(located.syntax().ident, "Foo");
    /// ```
    pub fn syntax(&self) -> &T {
        &self.syntax
    }

    /// Returns the locator associated with this syntax tree.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use syn_locator::Locate;
    ///
    /// let located = syn_locator::locate::<syn::ItemStruct>("file.rs", "struct Foo;").unwrap();
    ///
    /// assert_eq!(located.syntax().ident.code(located.locator()), "Foo");
    /// ```
    pub fn locator(&self) -> &Locator {
        &self.locator
    }

    /// Returns the recorded location for `node`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use syn_locator::Locate;
    ///
    /// let located = syn_locator::locate::<syn::ItemStruct>("file.rs", "struct Foo;").unwrap();
    ///
    /// let loc = located.location(&located.ident);
    /// assert_eq!(loc.start, 7);
    /// assert_eq!(loc.end, 10);
    /// ```
    pub fn location<N: Locate + ?Sized>(&self, node: &N) -> Location {
        node.location(&self.locator)
    }

    /// Returns a compact `path:line: source` message for `node`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use syn_locator::Locate;
    ///
    /// let located = syn_locator::locate::<syn::ItemStruct>("file.rs", "struct Foo;").unwrap();
    ///
    /// assert_eq!(located.location_message(&located.ident), "file.rs:1: Foo");
    /// ```
    pub fn location_message<N: Locate + ?Sized>(&self, node: &N) -> String {
        node.location_message(&self.locator)
    }

    /// Returns the exact source text recorded for `node`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use syn_locator::Locate;
    ///
    /// let located = syn_locator::locate::<syn::ItemStruct>("file.rs", "struct Foo;").unwrap();
    ///
    /// assert_eq!(located.code(&located.ident), "Foo");
    /// ```
    pub fn code<N: Locate + ?Sized>(&self, node: &N) -> String {
        node.code(&self.locator)
    }
}

impl<T: Locate> Deref for Located<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        self.syntax()
    }
}

/// Low-level entry point for recording locations into an explicit [`Locator`].
///
/// Prefer [`locate`] or [`Located::new`] unless you need to manage a locator yourself. Since
/// `Locator` keys nodes by address and type, keep the syntax tree at the same memory addresses for
/// as long as the locator is used.
pub trait LocateEntry: Locate {
    /// Records locations for this syntax tree in `locator`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use syn_locator::{Locate, LocateEntry, Locator};
    ///
    /// let code = "struct Foo;";
    /// let syntax = syn::parse_str::<syn::ItemStruct>(code).unwrap();
    /// let mut locator = Locator::new("file.rs", code);
    ///
    /// syntax.locate_as_entry(&mut locator).unwrap();
    ///
    /// assert_eq!(syntax.ident.code(&locator), "Foo");
    /// ```
    fn locate_as_entry(&self, locator: &mut Locator) -> Result<()> {
        let loc = locator.location(0, locator.get_original_code().len());
        locator.set_location(self, loc);
        let code = locator.filtered_code_ptr();

        // Safety: Locating only reads the filtered code. The stored Arc keeps this pointer
        // valid for the duration of the call.
        unsafe {
            let code = code.as_ref().unwrap_unchecked();
            self.locate(locator, code, 0);
        }

        Ok(())
    }
}

impl<T: Locate> LocateEntry for T {}

/// Provides source-location behavior for supported `syn` syntax nodes.
///
/// Most users call methods on [`Located`] instead of using this trait directly.
pub trait Locate: Any {
    /// Finds a location in the given file path, code, and offset.
    ///
    /// This is the low-level hook used by parent nodes while walking the syntax tree.
    ///
    /// # Examples
    ///
    /// ```rust,no_run
    /// use syn_locator::{Locate, LocateEntry, Locator};
    ///
    /// let code = "struct Foo;";
    /// let syntax = syn::parse_str::<syn::ItemStruct>(code).unwrap();
    /// let mut locator = Locator::new("file.rs", code);
    /// syntax.locate_as_entry(&mut locator).unwrap();
    ///
    /// let loc = syntax.find_loc(&mut locator, code, 0);
    /// assert_eq!(&code[loc.start..loc.end], code);
    /// ```
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location;

    /// Overrides this node's location in `locator`.
    ///
    /// # Examples
    ///
    /// ```rust,no_run
    /// use syn_locator::{Locate, LocateEntry, Locator, Location};
    ///
    /// let code = "struct Foo;";
    /// let syntax = syn::parse_str::<syn::ItemStruct>(code).unwrap();
    /// let mut locator = Locator::new("file.rs", code);
    /// syntax.locate_as_entry(&mut locator).unwrap();
    ///
    /// let loc = Location { start: 0, end: 0 };
    /// syntax.ident.relocate(&mut locator, loc);
    /// ```
    fn relocate(&self, locator: &mut Locator, loc: Location) {
        locator.set_location(self, loc);
    }

    /// Locates this node and stores the result in `locator`.
    ///
    /// Called by parent nodes while walking the syntax tree.
    ///
    /// # Examples
    ///
    /// ```rust,no_run
    /// use syn_locator::{Locate, LocateEntry, Locator};
    ///
    /// let code = "struct Foo;";
    /// let syntax = syn::parse_str::<syn::ItemStruct>(code).unwrap();
    /// let mut locator = Locator::new("file.rs", code);
    /// syntax.locate_as_entry(&mut locator).unwrap();
    ///
    /// let loc = syntax.ident.locate(&mut locator, code, 0);
    /// assert_eq!(&code[loc.start..loc.end], "Foo");
    /// ```
    fn locate(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        let loc = self.find_loc(locator, code, offset);
        locator.set_location(self, loc);
        loc
    }

    /// Returns this node's recorded location from `locator`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use syn_locator::Locate;
    ///
    /// let located = syn_locator::locate::<syn::ItemStruct>("file.rs", "struct Foo;").unwrap();
    ///
    /// let loc = located.ident.location(located.locator());
    /// assert_eq!(loc.start, 7);
    /// assert_eq!(loc.end, 10);
    /// ```
    fn location(&self, locator: &Locator) -> Location {
        self._location(locator)
    }

    /// Returns this node's recorded location from a specific [`Locator`].
    ///
    /// # Examples
    ///
    /// ```rust
    /// use syn_locator::Locate;
    ///
    /// let located = syn_locator::locate::<syn::ItemStruct>("file.rs", "struct Foo;").unwrap();
    ///
    /// let loc = located.ident._location(located.locator());
    /// assert_eq!(loc.start, 7);
    /// assert_eq!(loc.end, 10);
    /// ```
    fn _location(&self, locator: &Locator) -> Location {
        locator.get_location(self).unwrap_or_else(|| {
            panic!(
                "failed to find the location of `{}`. did you forget `Locate::locate`?",
                any::type_name::<Self>()
            )
        })
    }

    /// Returns a compact `path:line: source` message for this node.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use syn_locator::Locate;
    ///
    /// let located = syn_locator::locate::<syn::ItemStruct>("file.rs", "struct Foo;").unwrap();
    ///
    /// assert_eq!(located.ident.location_message(located.locator()), "file.rs:1: Foo");
    /// ```
    fn location_message(&self, locator: &Locator) -> String {
        (|| {
            let loc = locator.get_location(self)?;
            let path = locator.file_path();
            let code = locator.get_original_code();
            let line = code.as_bytes()[..loc.start]
                .iter()
                .filter(|&&b| b == b'\n')
                .count()
                + 1;
            let content = &code[loc.start..loc.end];
            Some(format!("{path}:{line}: {content}"))
        })()
        .unwrap_or_else(|| {
            panic!(
                "failed to find the location of `{}`. did you forget `Locate::locate`?",
                any::type_name::<Self>()
            )
        })
    }

    /// Returns the exact source text recorded for this node.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use syn_locator::Locate;
    ///
    /// let located = syn_locator::locate::<syn::ItemStruct>("file.rs", "struct Foo;").unwrap();
    ///
    /// assert_eq!(located.ident.code(located.locator()), "Foo");
    /// ```
    fn code(&self, locator: &Locator) -> String {
        (|| {
            let loc = locator.get_location(self)?;
            let code = locator.get_original_code();
            let content = &code[loc.start..loc.end];
            Some(content.to_owned())
        })()
        .unwrap_or_else(|| {
            panic!(
                "failed to find the location of `{}`. did you forget `Locate::locate`?",
                any::type_name::<Self>()
            )
        })
    }
}

/// Locates a group of child nodes as a single range.
///
/// This is a public implementation helper used by `Locate` implementations.
pub trait LocateGroup {
    /// Locates all nodes in the group and returns their combined range.
    ///
    /// # Examples
    ///
    /// ```rust,no_run
    /// use syn_locator::{Locate, LocateEntry, LocateGroup, Locator};
    ///
    /// let code = "struct Foo;";
    /// let syntax = syn::parse_str::<syn::ItemStruct>(code).unwrap();
    /// let mut locator = Locator::new("file.rs", code);
    /// syntax.locate_as_entry(&mut locator).unwrap();
    ///
    /// let loc = (&syntax.struct_token, &syntax.ident).locate_as_group(&mut locator, code, 0);
    /// assert_eq!(loc.start, 0);
    /// ```
    fn locate_as_group(&self, locator: &mut Locator, code: &str, offset: usize) -> Location;
    /// Assigns the same location to every node in the group.
    ///
    /// # Examples
    ///
    /// ```rust,no_run
    /// use syn_locator::{Locate, LocateEntry, LocateGroup, Locator, Location};
    ///
    /// let code = "struct Foo;";
    /// let syntax = syn::parse_str::<syn::ItemStruct>(code).unwrap();
    /// let mut locator = Locator::new("file.rs", code);
    /// syntax.locate_as_entry(&mut locator).unwrap();
    /// let loc = Location { start: 0, end: 0 };
    /// (&syntax.struct_token, &syntax.ident).relocate_as_group(&mut locator, loc);
    /// ```
    fn relocate_as_group(&self, locator: &mut Locator, loc: Location);
}

macro_rules! impl_locate_group {
    ( $($i:expr),* ; $($ri:expr),* ) => {
        paste::paste! {
            impl<'a, $([<A $i>]: Locate),*> LocateGroup for ( $( &'a [<A $i>] ),* ) {
                #[allow(unused_assignments)]
                fn locate_as_group(
                    &self,
                    locator: &mut Locator,
                    code: &str,
                    offset: usize
                ) -> Location
                {
                    let ( $( [<this $i>] ),* ) = self;

                    // Locates children and tracks the group's end.
                    let mut end = offset;
                    $(
                        let [<loc $i>] = [<this $i>].locate(locator, code, end);
                        if [<loc $i>].start < [<loc $i>].end {
                            end = end.max( [<loc $i>].end );
                        }
                    )*

                    // Determine the start of this group.
                    let mut start = usize::MAX;
                    $(
                        if [<loc $i>].start != [<loc $i>].end {
                            start = start.min( [<loc $i>].start );
                        }
                    )*
                    if start == usize::MAX {
                        start = offset;
                    }

                    // Move empty children to the closest non-empty child.
                    let mut cur = end;
                    $(
                        if [<loc $ri>].start >= [<loc $ri>].end {
                            [<this $ri>].relocate(locator, Location {
                                start: cur,
                                end: cur
                            });
                        } else {
                            cur = [<loc $ri>].start;
                        }
                    )*

                    Location {
                        start,
                        end
                    }
                }

                fn relocate_as_group(&self, locator: &mut Locator, loc: Location) {
                    let ( $( [<this $i>] ),* ) = self;

                    // Propagate relocation to children.
                    $(
                        [<this $i>].relocate(locator, loc);
                    )*
                }
            }
        }
    };
}

impl LocateGroup for () {
    fn locate_as_group(&self, _locator: &mut Locator, _code: &str, offset: usize) -> Location {
        Location {
            start: offset,
            end: offset,
        }
    }

    fn relocate_as_group(&self, _: &mut Locator, _: Location) {}
}

impl<T: Locate> LocateGroup for &T {
    fn locate_as_group(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        self.locate(locator, code, offset)
    }

    fn relocate_as_group(&self, locator: &mut Locator, loc: Location) {
        self.relocate(locator, loc)
    }
}

impl_locate_group!(0, 1 ; 1, 0);
impl_locate_group!(0, 1, 2 ; 2, 1, 0);
impl_locate_group!(0, 1, 2, 3 ; 3, 2, 1, 0);
impl_locate_group!(0, 1, 2, 3, 4 ; 4, 3, 2, 1, 0);
impl_locate_group!(0, 1, 2, 3, 4, 5 ; 5, 4, 3, 2, 1, 0);
impl_locate_group!(0, 1, 2, 3, 4, 5, 6 ; 6, 5, 4, 3, 2, 1, 0);
impl_locate_group!(0, 1, 2, 3, 4, 5, 6, 7 ; 7, 6, 5, 4, 3, 2, 1, 0);
impl_locate_group!(0, 1, 2, 3, 4, 5, 6, 7, 8 ; 8, 7, 6, 5, 4, 3, 2, 1, 0);
impl_locate_group!(0, 1, 2, 3, 4, 5, 6, 7, 8, 9 ; 9, 8, 7, 6, 5, 4, 3, 2, 1, 0);
impl_locate_group!(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10 ; 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0);
impl_locate_group!(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11 ; 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0);

/// Helper for locating syntax surrounded by a paired token.
///
/// This is used by `Locate` implementations for braces, brackets, and parentheses.
pub struct Surround<'s, F, S, I, B> {
    /// Nodes that appear before the surrounding token.
    pub front: F,
    /// The paired token that surrounds `inner`.
    pub surround: &'s S,
    /// Nodes inside the surrounding token.
    pub inner: I,
    /// Nodes that appear after the surrounding token.
    pub back: B,
}

impl<F, S, I, B> Surround<'_, F, S, I, B>
where
    F: LocateGroup,
    S: Locate,
    I: LocateGroup,
    B: LocateGroup,
{
    /// Locates the surrounding token, its inner nodes, and adjacent groups.
    ///
    /// # Examples
    ///
    /// ```rust,no_run
    /// use syn_locator::{Locate, LocateEntry, Locator, Surround};
    ///
    /// let code = "{ value }";
    /// let syntax = syn::parse_str::<syn::Block>(code).unwrap();
    /// let mut locator = Locator::new("block.rs", code);
    /// syntax.locate_as_entry(&mut locator).unwrap();
    /// let helper = Surround {
    ///     front: (),
    ///     surround: &syntax.brace_token,
    ///     inner: &syntax.stmts,
    ///     back: (),
    /// };
    /// let loc = helper.locate(&mut locator, code, 0);
    /// assert_eq!(loc.start, 0);
    /// ```
    pub fn locate(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        // Locate the surrounding token and fields.
        let front_loc = self.front.locate_as_group(locator, code, offset);
        let surround_loc = self.surround.locate(locator, code, front_loc.end);
        self.inner
            .locate_as_group(locator, code, surround_loc.start + 1);
        let back_loc = self.back.locate_as_group(locator, code, surround_loc.end);

        // Move an empty front group to the surrounding token.
        let mut start = front_loc.start;
        if front_loc.start == front_loc.end {
            self.front.relocate_as_group(
                locator,
                Location {
                    start: surround_loc.start,
                    end: surround_loc.start,
                },
            );
            start = surround_loc.start;
        }

        // Move an empty back group to the surrounding token.
        let mut end = back_loc.end;
        if back_loc.start == back_loc.end {
            self.back.relocate_as_group(
                locator,
                Location {
                    start: surround_loc.end,
                    end: surround_loc.end,
                },
            );
            end = surround_loc.end;
        }

        Location { start, end }
    }
}

/// Helper for locating qualified paths that contain a [`syn::QSelf`].
pub struct Qualified<'a, F, B> {
    /// Nodes that appear before the qualified self type.
    pub front: F,
    /// The qualified self type, such as `<T as Trait>`.
    pub qself: &'a syn::QSelf,
    /// The path associated with `qself`.
    pub path: &'a syn::Path,
    /// Nodes that appear after the path.
    pub back: B,
}

impl<F, B> Qualified<'_, F, B>
where
    F: LocateGroup,
    B: LocateGroup,
{
    /// Locates a qualified self type together with its associated path.
    ///
    /// # Examples
    ///
    /// ```rust,no_run
    /// use syn_locator::{Locate, LocateEntry, Locator, Qualified};
    ///
    /// let code = "type Assoc = <T as Trait>::Item;";
    /// let syntax = syn::parse_str::<syn::ItemType>(code).unwrap();
    /// let mut locator = Locator::new("qualified.rs", code);
    /// syntax.locate_as_entry(&mut locator).unwrap();
    /// let syn::Type::Path(type_path) = syntax.ty.as_ref() else {
    ///     unreachable!()
    /// };
    /// let qself = type_path.qself.as_ref().unwrap();
    /// let helper = Qualified { front: (), qself, path: &type_path.path, back: () };
    ///
    /// let loc = helper.locate(&mut locator, code, 13);
    /// assert_eq!(loc.start, 13);
    /// ```
    pub fn locate(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        // Locate the qualified self type and path.
        let front_loc = self.front.locate_as_group(locator, code, offset);

        let qself_loc = self.qself.locate(locator, code, front_loc.end);
        let qself_mid_loc = self.qself.as_token._location(locator);

        // The path search starts in text like `a::b::Trait>::Assoc`. The extra `>` is fine
        // because string matching skips over it.
        let path_loc = self.path.locate(locator, code, qself_mid_loc.end);

        let back_loc = self.back.locate_as_group(locator, code, path_loc.end);

        // Move an empty front group to the qualified self type.
        let mut start = front_loc.start;
        if front_loc.start == front_loc.end {
            self.front.relocate_as_group(
                locator,
                Location {
                    start: qself_loc.start,
                    end: qself_loc.start,
                },
            );
            start = qself_loc.start;
        }

        // Move an empty back group to the path.
        let mut end = back_loc.end;
        if back_loc.start == back_loc.end {
            self.back.relocate_as_group(
                locator,
                Location {
                    start: path_loc.end,
                    end: path_loc.end,
                },
            );
            end = path_loc.end;
        }

        Location { start, end }
    }
}

/// Storage for one source file and its syntax-node locations.
///
/// Most users do not need this type directly because [`Located`] owns one internally.
pub struct Locator {
    file_path: String,
    content: Content,
    map: Map<LocationKey, Location>,
}

impl Locator {
    /// Creates a locator for one source file.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use syn_locator::{Locate, LocateEntry, Locator};
    ///
    /// let code = "struct Foo;";
    /// let syntax = syn::parse_str::<syn::ItemStruct>(code).unwrap();
    /// let mut locator = Locator::new("file.rs", code);
    ///
    /// syntax.locate_as_entry(&mut locator).unwrap();
    ///
    /// assert_eq!(syntax.ident.code(&locator), "Foo");
    /// ```
    pub fn new(file_path: &str, code: impl Into<Box<str>>) -> Self {
        let code = code.into();
        Self {
            file_path: file_path.to_owned(),
            content: Content::new(code),
            map: Map::default(),
        }
    }

    /// Returns the file path associated with this locator.
    ///
    /// # Examples
    ///
    /// ```rust
    /// let located = syn_locator::locate::<syn::ItemStruct>("file.rs", "struct Foo;").unwrap();
    ///
    /// assert_eq!(located.locator().file_path(), "file.rs");
    /// ```
    pub fn file_path(&self) -> &str {
        &self.file_path
    }

    fn location(&self, start: usize, end: usize) -> Location {
        Location { start, end }
    }

    fn set_location<T: Any + ?Sized>(&mut self, syn_node: &T, loc: Location) {
        self.map.insert(LocationKey::new(syn_node), loc);
    }

    fn get_location<T: Any + ?Sized>(&self, syn_node: &T) -> Option<Location> {
        self.map.get(&LocationKey::new(syn_node)).cloned()
    }

    fn get_original_code(&self) -> &str {
        &self.content.original_code
    }

    fn filtered_code_ptr(&self) -> *const str {
        let code: &str = &self.content.filtered_code;
        code as *const str
    }
}

struct Content {
    original_code: Box<str>,
    filtered_code: Box<str>,
}

impl Content {
    fn new(code: Box<str>) -> Self {
        let filtered_code = CommentReplacer.replace((*code).as_ref());
        let filtered_code: Box<str> = filtered_code.into();

        Self {
            original_code: code,
            filtered_code,
        }
    }
}

#[derive(Debug, Clone, Copy, Default)]
struct CommentReplacer;

impl CommentReplacer {
    /// Replaces comments with white spaces from the given code for further token matching.
    fn replace(self, code: &str) -> Cow<'_, str> {
        let bytes = code.as_bytes();
        let mut filtered = None;
        let mut i = 0;

        while i < bytes.len() {
            if let Some(end) = self.string_literal_end(bytes, i) {
                // ignores string-like literal
                i = end;
            } else if let Some(end) = self.char_literal_end(bytes, i) {
                // ignores char-like literal
                i = end;
            } else if bytes[i..].starts_with(b"//") {
                let end = self.line_comment_end(bytes, i + 2);
                self.blank_out(&mut filtered, code, i, end);
                i = end;
            } else if bytes[i..].starts_with(b"/*") {
                let end = self.block_comment_end(bytes, i + 2);
                self.blank_out(&mut filtered, code, i, end);
                i = end;
            } else {
                i += 1;
            }
        }

        filtered.map_or(Cow::Borrowed(code), |filtered| {
            Cow::Owned(String::from_utf8(filtered).unwrap())
        })
    }

    /// Replaces the given code range with white spaces.
    fn blank_out(self, filtered: &mut Option<Vec<u8>>, code: &str, start: usize, end: usize) {
        let filtered = filtered.get_or_insert_with(|| code.as_bytes().to_vec());

        for byte in &mut filtered[start..end] {
            *byte = b' ';
        }
    }

    /// Finds the end of a line comment.
    fn line_comment_end(self, bytes: &[u8], mut i: usize) -> usize {
        while i < bytes.len() && bytes[i] != b'\n' {
            i += 1;
        }
        i
    }

    /// Finds the end of a block comment.
    fn block_comment_end(self, bytes: &[u8], mut i: usize) -> usize {
        let mut depth = 1;

        while i + 1 < bytes.len() {
            if bytes[i..].starts_with(b"/*") {
                depth += 1;
                i += 2;
            } else if bytes[i..].starts_with(b"*/") {
                depth -= 1;
                i += 2;

                if depth == 0 {
                    return i;
                }
            } else {
                i += 1;
            }
        }

        bytes.len()
    }

    /// Identifies string-like literals and returns the end of the literals.
    fn string_literal_end(self, bytes: &[u8], i: usize) -> Option<usize> {
        if let Some(end) = self.raw_string_literal_end(bytes, i) {
            Some(end)
        } else if bytes[i] == b'"' {
            Some(self.quoted_literal_end(bytes, i + 1, b'"'))
        } else if bytes[i..].starts_with(b"b\"") || bytes[i..].starts_with(b"c\"") {
            Some(self.quoted_literal_end(bytes, i + 2, b'"'))
        } else {
            None
        }
    }

    /// Identifies raw string literals like r"..", br"..", or cr".." and returns the end of the
    /// literals.
    fn raw_string_literal_end(self, bytes: &[u8], i: usize) -> Option<usize> {
        let prefix_len = if bytes[i] == b'r' {
            1
        } else if bytes[i..].starts_with(b"br") || bytes[i..].starts_with(b"cr") {
            2
        } else {
            return None;
        };

        let mut hashes = 0;
        let mut cursor = i + prefix_len;
        while cursor < bytes.len() && bytes[cursor] == b'#' {
            hashes += 1;
            cursor += 1;
        }

        if cursor >= bytes.len() || bytes[cursor] != b'"' {
            return None;
        }

        cursor += 1;
        while cursor < bytes.len() {
            if bytes[cursor] == b'"' {
                let close_start = cursor + 1;
                let close_end = close_start + hashes;

                if close_end <= bytes.len()
                    && bytes[close_start..close_end].iter().all(|&b| b == b'#')
                {
                    return Some(close_end);
                }
            }

            cursor += 1;
        }

        Some(bytes.len())
    }

    /// Identifies char-like literals and returns the end byte of the literals.
    fn char_literal_end(self, bytes: &[u8], i: usize) -> Option<usize> {
        if bytes[i] == b'\'' {
            self.char_literal_end_after_open_quote(bytes, i + 1)
        } else if bytes[i..].starts_with(b"b'") {
            self.char_literal_end_after_open_quote(bytes, i + 2)
        } else {
            None
        }
    }

    /// Finds the end of char-like literals after an open quote.
    fn char_literal_end_after_open_quote(self, bytes: &[u8], i: usize) -> Option<usize> {
        if i >= bytes.len() || bytes[i] == b'\'' || bytes[i] == b'\n' {
            return None;
        }

        let end = if bytes[i] == b'\\' {
            self.escaped_char_end(bytes, i + 1)?
        } else {
            i + self.utf8_char_width(bytes[i])?
        };

        if end < bytes.len() && bytes[end] == b'\'' {
            Some(end + 1)
        } else {
            None
        }
    }

    /// Finds the end of char-like literals after a backslash.
    fn escaped_char_end(self, bytes: &[u8], i: usize) -> Option<usize> {
        if i >= bytes.len() || bytes[i] == b'\n' {
            return None;
        }

        // Detects Unicode escape from '\u{...}'
        if bytes[i] == b'u' && bytes.get(i + 1) == Some(&b'{') {
            let mut cursor = i + 2;

            while cursor < bytes.len() && bytes[cursor] != b'\n' {
                if bytes[cursor] == b'}' {
                    return Some(cursor + 1);
                }

                cursor += 1;
            }

            None
        }
        // Detects 1 byte ASICC escape from '/xNN'
        else if bytes[i] == b'x' {
            Some((i + 3).min(bytes.len()))
        } else {
            Some(i + 1)
        }
    }

    fn utf8_char_width(self, byte: u8) -> Option<usize> {
        if byte < 0x80 {
            Some(1)
        } else if byte & 0b1110_0000 == 0b1100_0000 {
            Some(2)
        } else if byte & 0b1111_0000 == 0b1110_0000 {
            Some(3)
        } else if byte & 0b1111_1000 == 0b1111_0000 {
            Some(4)
        } else {
            None
        }
    }

    /// Finds the end of ordinary quoted literals.
    fn quoted_literal_end(self, bytes: &[u8], mut i: usize, quote: u8) -> usize {
        while i < bytes.len() {
            if bytes[i] == b'\\' {
                i += 2;
            } else if bytes[i] == quote {
                return i + 1;
            } else {
                i += 1;
            }
        }

        bytes.len()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct LocationKey {
    /// For hashing.
    ptr: usize,

    // The type id distinguishes a struct from its first field when both have the same address.
    ty: TypeId,
}

impl LocationKey {
    fn new<T: Any + ?Sized>(t: &T) -> Self {
        Self {
            ptr: t as *const T as *const () as usize,
            ty: TypeId::of::<T>(),
        }
    }
}

/// Byte range for a syntax node in the locator's source file.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Location {
    /// Byte index into the code.
    pub start: usize,

    /// Exclusive byte index into the code.
    pub end: usize,
}

macro_rules! impl_locate_for_token {
    ($ty:ty, $token:literal, char) => {
        impl Locate for $ty {
            fn find_loc(&self, _locator: &mut Locator, code: &str, offset: usize) -> Location {
                helper::char_location(code, offset, $token)
            }
        }
    };
    ($ty:ty, $token:literal, str) => {
        impl Locate for $ty {
            fn find_loc(&self, _locator: &mut Locator, code: &str, offset: usize) -> Location {
                helper::str_location(code, offset, $token)
            }
        }
    };
}

impl_locate_for_token!(syn::Token![abstract], "abstract", str);
impl_locate_for_token!(syn::Token![as], "as", str);
impl_locate_for_token!(syn::Token![async], "async", str);
impl_locate_for_token!(syn::Token![auto], "auto", str);
impl_locate_for_token!(syn::Token![await], "await", str);
impl_locate_for_token!(syn::Token![become], "become", str);
impl_locate_for_token!(syn::Token![box], "box", str);
impl_locate_for_token!(syn::Token![break], "break", str);
impl_locate_for_token!(syn::Token![const], "const", str);
impl_locate_for_token!(syn::Token![continue], "continue", str);
impl_locate_for_token!(syn::Token![crate], "crate", str);
impl_locate_for_token!(syn::Token![default], "default", str);
impl_locate_for_token!(syn::Token![do], "do", str);
impl_locate_for_token!(syn::Token![dyn], "dyn", str);
impl_locate_for_token!(syn::Token![else], "else", str);
impl_locate_for_token!(syn::Token![enum], "enum", str);
impl_locate_for_token!(syn::Token![extern], "extern", str);
impl_locate_for_token!(syn::Token![final], "final", str);
impl_locate_for_token!(syn::Token![fn], "fn", str);
impl_locate_for_token!(syn::Token![for], "for", str);
impl_locate_for_token!(syn::Token![if], "if", str);
impl_locate_for_token!(syn::Token![impl], "impl", str);
impl_locate_for_token!(syn::Token![in], "in", str);
impl_locate_for_token!(syn::Token![let], "let", str);
impl_locate_for_token!(syn::Token![loop], "loop", str);
impl_locate_for_token!(syn::Token![macro], "macro", str);
impl_locate_for_token!(syn::Token![match], "match", str);
impl_locate_for_token!(syn::Token![mod], "mod", str);
impl_locate_for_token!(syn::Token![move], "move", str);
impl_locate_for_token!(syn::Token![mut], "mut", str);
impl_locate_for_token!(syn::Token![override], "override", str);
impl_locate_for_token!(syn::Token![priv], "priv", str);
impl_locate_for_token!(syn::Token![pub], "pub", str);
impl_locate_for_token!(syn::Token![raw], "raw", str);
impl_locate_for_token!(syn::Token![ref], "ref", str);
impl_locate_for_token!(syn::Token![return], "return", str);
impl_locate_for_token!(syn::Token![Self], "Self", str);
impl_locate_for_token!(syn::Token![self], "self", str);
impl_locate_for_token!(syn::Token![static], "static", str);
impl_locate_for_token!(syn::Token![struct], "struct", str);
impl_locate_for_token!(syn::Token![super], "super", str);
impl_locate_for_token!(syn::Token![trait], "trait", str);
impl_locate_for_token!(syn::Token![try], "try", str);
impl_locate_for_token!(syn::Token![type], "type", str);
impl_locate_for_token!(syn::Token![typeof], "typeof", str);
impl_locate_for_token!(syn::Token![union], "union", str);
impl_locate_for_token!(syn::Token![unsafe], "unsafe", str);
impl_locate_for_token!(syn::Token![unsized], "unsized", str);
impl_locate_for_token!(syn::Token![use], "use", str);
impl_locate_for_token!(syn::Token![virtual], "virtual", str);
impl_locate_for_token!(syn::Token![where], "where", str);
impl_locate_for_token!(syn::Token![while], "while", str);
impl_locate_for_token!(syn::Token![yield], "yield", str);
impl_locate_for_token!(syn::Token![&], '&', char);
impl_locate_for_token!(syn::Token![&&], "&&", str);
impl_locate_for_token!(syn::Token![&=], "&=", str);
impl_locate_for_token!(syn::Token![@], '@', char);
impl_locate_for_token!(syn::Token![^], '^', char);
impl_locate_for_token!(syn::Token![^=], "^=", str);
impl_locate_for_token!(syn::Token![:], ':', char);
impl_locate_for_token!(syn::Token![,], ',', char);
impl_locate_for_token!(syn::Token![$], '$', char);
impl_locate_for_token!(syn::Token![.], '.', char);
impl_locate_for_token!(syn::Token![..], "..", str);
impl_locate_for_token!(syn::Token![...], "...", str);
impl_locate_for_token!(syn::Token![..=], "..=", str);
impl_locate_for_token!(syn::Token![=], '=', char);
impl_locate_for_token!(syn::Token![==], "==", str);
impl_locate_for_token!(syn::Token![=>], "=>", str);
impl_locate_for_token!(syn::Token![>=], ">=", str);
impl_locate_for_token!(syn::Token![>], '>', char);
impl_locate_for_token!(syn::Token![<-], "<-", str);
impl_locate_for_token!(syn::Token![<=], "<=", str);
impl_locate_for_token!(syn::Token![<], '<', char);
impl_locate_for_token!(syn::Token![-], '-', char);
impl_locate_for_token!(syn::Token![-=], "-=", str);
impl_locate_for_token!(syn::Token![!=], "!=", str);
impl_locate_for_token!(syn::Token![!], '!', char);
impl_locate_for_token!(syn::Token![|], '|', char);
impl_locate_for_token!(syn::Token![|=], "|=", str);
impl_locate_for_token!(syn::Token![||], "||", str);
impl_locate_for_token!(syn::Token![::], "::", str);
impl_locate_for_token!(syn::Token![%], '%', char);
impl_locate_for_token!(syn::Token![%=], "%=", str);
impl_locate_for_token!(syn::Token![+], '+', char);
impl_locate_for_token!(syn::Token![+=], "+=", str);
impl_locate_for_token!(syn::Token![#], '#', char);
impl_locate_for_token!(syn::Token![?], '?', char);
impl_locate_for_token!(syn::Token![->], "->", str);
impl_locate_for_token!(syn::Token![;], ';', char);
impl_locate_for_token!(syn::Token![<<], "<<", str);
impl_locate_for_token!(syn::Token![<<=], "<<=", str);
impl_locate_for_token!(syn::Token![>>], ">>", str);
impl_locate_for_token!(syn::Token![>>=], ">>=", str);
impl_locate_for_token!(syn::Token![/], '/', char);
impl_locate_for_token!(syn::Token![/=], "/=", str);
impl_locate_for_token!(syn::Token![*], '*', char);
impl_locate_for_token!(syn::Token![*=], "*=", str);
impl_locate_for_token!(syn::Token![~], '~', char);
impl_locate_for_token!(syn::Token![_], '_', char);

impl Locate for syn::token::Group {
    fn find_loc(&self, _locator: &mut Locator, _code: &str, offset: usize) -> Location {
        Location {
            start: offset,
            end: offset,
        }
    }
}

macro_rules! impl_locate_for_pair_tokens {
    ($ty:ty, $open:literal, $close:literal) => {
        impl Locate for $ty {
            fn find_loc(&self, _locator: &mut Locator, code: &str, offset: usize) -> Location {
                const OPEN: char = $open;
                const CLOSE: char = $close;

                let cur_code = &code[offset..];

                let mut start = 0;
                let mut end = 0;
                let mut cur = offset;
                let mut level = 0;

                for c in cur_code.chars() {
                    if c == OPEN {
                        if level == 0 {
                            start = cur;
                        }
                        level += 1;
                    } else if c == CLOSE {
                        if level == 1 {
                            end = cur + CLOSE.len_utf8();
                            break;
                        }
                        if level > 0 {
                            level -= 1;
                        }
                    }
                    cur += c.len_utf8();
                }

                if start >= end {
                    panic!("expected `{OPEN}..{CLOSE}` from {cur_code}");
                }

                Location { start, end }
            }
        }
    };
}

impl_locate_for_pair_tokens!(syn::token::Brace, '{', '}');
impl_locate_for_pair_tokens!(syn::token::Bracket, '[', ']');
impl_locate_for_pair_tokens!(syn::token::Paren, '(', ')');

impl Locate for syn::Abi {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        (&self.extern_token, &self.name).locate_as_group(locator, code, offset)
    }
}

impl Locate for syn::AngleBracketedGenericArguments {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        (
            &self.colon2_token,
            &self.lt_token,
            &self.args,
            &self.gt_token,
        )
            .locate_as_group(locator, code, offset)
    }
}

impl Locate for syn::Arm {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        if let Some((if_token, guard)) = &self.guard {
            (
                &self.attrs,
                &self.pat,
                if_token,
                guard,
                &self.fat_arrow_token,
                &self.body,
                &self.comma,
            )
                .locate_as_group(locator, code, offset)
        } else {
            (
                &self.attrs,
                &self.pat,
                &self.fat_arrow_token,
                &self.body,
                &self.comma,
            )
                .locate_as_group(locator, code, offset)
        }
    }
}

impl Locate for syn::AssocConst {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        (&self.ident, &self.generics, &self.eq_token, &self.value)
            .locate_as_group(locator, code, offset)
    }
}

impl Locate for syn::AssocType {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        (&self.ident, &self.generics, &self.eq_token, &self.ty)
            .locate_as_group(locator, code, offset)
    }
}

impl Locate for syn::Attribute {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        Surround {
            front: (&self.pound_token, &self.style),
            surround: &self.bracket_token,
            inner: &self.meta,
            back: (),
        }
        .locate(locator, code, offset)
    }
}

impl Locate for syn::AttrStyle {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        match self {
            Self::Outer => Location {
                start: offset,
                end: offset,
            },
            Self::Inner(v) => v.find_loc(locator, code, offset),
        }
    }
}

impl Locate for syn::BareFnArg {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        if let Some((name, colon_token)) = &self.name {
            (&self.attrs, name, colon_token, &self.ty).locate_as_group(locator, code, offset)
        } else {
            (&self.attrs, &self.ty).locate_as_group(locator, code, offset)
        }
    }
}

impl Locate for syn::BareVariadic {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        if let Some((name, colon_token)) = &self.name {
            (&self.attrs, name, colon_token, &self.dots, &self.comma)
                .locate_as_group(locator, code, offset)
        } else {
            (&self.attrs, &self.dots, &self.comma).locate_as_group(locator, code, offset)
        }
    }
}

impl Locate for syn::BinOp {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        match self {
            Self::Add(v) => v.locate(locator, code, offset),
            Self::Sub(v) => v.locate(locator, code, offset),
            Self::Mul(v) => v.locate(locator, code, offset),
            Self::Div(v) => v.locate(locator, code, offset),
            Self::Rem(v) => v.locate(locator, code, offset),
            Self::And(v) => v.locate(locator, code, offset),
            Self::Or(v) => v.locate(locator, code, offset),
            Self::BitXor(v) => v.locate(locator, code, offset),
            Self::BitAnd(v) => v.locate(locator, code, offset),
            Self::BitOr(v) => v.locate(locator, code, offset),
            Self::Shl(v) => v.locate(locator, code, offset),
            Self::Shr(v) => v.locate(locator, code, offset),
            Self::Eq(v) => v.locate(locator, code, offset),
            Self::Lt(v) => v.locate(locator, code, offset),
            Self::Le(v) => v.locate(locator, code, offset),
            Self::Ne(v) => v.locate(locator, code, offset),
            Self::Ge(v) => v.locate(locator, code, offset),
            Self::Gt(v) => v.locate(locator, code, offset),
            Self::AddAssign(v) => v.locate(locator, code, offset),
            Self::SubAssign(v) => v.locate(locator, code, offset),
            Self::MulAssign(v) => v.locate(locator, code, offset),
            Self::DivAssign(v) => v.locate(locator, code, offset),
            Self::RemAssign(v) => v.locate(locator, code, offset),
            Self::BitXorAssign(v) => v.locate(locator, code, offset),
            Self::BitAndAssign(v) => v.locate(locator, code, offset),
            Self::BitOrAssign(v) => v.locate(locator, code, offset),
            Self::ShlAssign(v) => v.locate(locator, code, offset),
            Self::ShrAssign(v) => v.locate(locator, code, offset),
            _ => Location {
                start: offset,
                end: offset,
            },
        }
    }
}

impl Locate for syn::Block {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        Surround {
            front: (),
            surround: &self.brace_token,
            inner: &self.stmts,
            back: (),
        }
        .locate(locator, code, offset)
    }
}

impl Locate for syn::BoundLifetimes {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        (
            &self.for_token,
            &self.lt_token,
            &self.lifetimes,
            &self.gt_token,
        )
            .locate_as_group(locator, code, offset)
    }
}

impl Locate for syn::CapturedParam {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        match self {
            Self::Lifetime(v) => v.locate(locator, code, offset),
            Self::Ident(v) => v.locate(locator, code, offset),
            _ => Location {
                start: offset,
                end: offset,
            },
        }
    }
}

impl Locate for syn::ConstParam {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        (
            &self.attrs,
            &self.const_token,
            &self.ident,
            &self.colon_token,
            &self.ty,
            &self.eq_token,
            &self.default,
        )
            .locate_as_group(locator, code, offset)
    }
}

impl Locate for syn::Constraint {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        (&self.ident, &self.generics, &self.colon_token, &self.bounds)
            .locate_as_group(locator, code, offset)
    }
}

impl Locate for syn::Expr {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        match self {
            Self::Array(v) => v.locate(locator, code, offset),
            Self::Assign(v) => v.locate(locator, code, offset),
            Self::Async(v) => v.locate(locator, code, offset),
            Self::Await(v) => v.locate(locator, code, offset),
            Self::Binary(v) => v.locate(locator, code, offset),
            Self::Block(v) => v.locate(locator, code, offset),
            Self::Break(v) => v.locate(locator, code, offset),
            Self::Call(v) => v.locate(locator, code, offset),
            Self::Cast(v) => v.locate(locator, code, offset),
            Self::Closure(v) => v.locate(locator, code, offset),
            Self::Const(v) => v.locate(locator, code, offset),
            Self::Continue(v) => v.locate(locator, code, offset),
            Self::Field(v) => v.locate(locator, code, offset),
            Self::ForLoop(v) => v.locate(locator, code, offset),
            Self::Group(v) => v.locate(locator, code, offset),
            Self::If(v) => v.locate(locator, code, offset),
            Self::Index(v) => v.locate(locator, code, offset),
            Self::Infer(v) => v.locate(locator, code, offset),
            Self::Let(v) => v.locate(locator, code, offset),
            Self::Lit(v) => v.locate(locator, code, offset),
            Self::Loop(v) => v.locate(locator, code, offset),
            Self::Macro(v) => v.locate(locator, code, offset),
            Self::Match(v) => v.locate(locator, code, offset),
            Self::MethodCall(v) => v.locate(locator, code, offset),
            Self::Paren(v) => v.locate(locator, code, offset),
            Self::Path(v) => v.locate(locator, code, offset),
            Self::Range(v) => v.locate(locator, code, offset),
            Self::RawAddr(v) => v.locate(locator, code, offset),
            Self::Reference(v) => v.locate(locator, code, offset),
            Self::Repeat(v) => v.locate(locator, code, offset),
            Self::Return(v) => v.locate(locator, code, offset),
            Self::Struct(v) => v.locate(locator, code, offset),
            Self::Try(v) => v.locate(locator, code, offset),
            Self::TryBlock(v) => v.locate(locator, code, offset),
            Self::Tuple(v) => v.locate(locator, code, offset),
            Self::Unary(v) => v.locate(locator, code, offset),
            Self::Unsafe(v) => v.locate(locator, code, offset),
            Self::Verbatim(_) => Location {
                start: offset,
                end: offset,
            },
            Self::While(v) => v.locate(locator, code, offset),
            Self::Yield(v) => v.locate(locator, code, offset),
            _ => Location {
                start: offset,
                end: offset,
            },
        }
    }
}

impl Locate for syn::ExprArray {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        Surround {
            front: &self.attrs,
            surround: &self.bracket_token,
            inner: &self.elems,
            back: (),
        }
        .locate(locator, code, offset)
    }
}

impl Locate for syn::ExprAssign {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        (&self.attrs, &self.left, &self.eq_token, &self.right)
            .locate_as_group(locator, code, offset)
    }
}

impl Locate for syn::ExprAsync {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        (&self.attrs, &self.async_token, &self.capture, &self.block)
            .locate_as_group(locator, code, offset)
    }
}

impl Locate for syn::ExprAwait {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        (&self.attrs, &self.base, &self.dot_token, &self.await_token)
            .locate_as_group(locator, code, offset)
    }
}

impl Locate for syn::ExprBinary {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        (&self.attrs, &self.left, &self.op, &self.right).locate_as_group(locator, code, offset)
    }
}

impl Locate for syn::ExprBlock {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        (&self.attrs, &self.label, &self.block).locate_as_group(locator, code, offset)
    }
}

impl Locate for syn::ExprBreak {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        (&self.attrs, &self.break_token, &self.label, &self.expr)
            .locate_as_group(locator, code, offset)
    }
}

impl Locate for syn::ExprCall {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        Surround {
            front: (&self.attrs, &self.func),
            surround: &self.paren_token,
            inner: &self.args,
            back: (),
        }
        .locate(locator, code, offset)
    }
}

impl Locate for syn::ExprCast {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        (&self.attrs, &self.expr, &self.as_token, &self.ty).locate_as_group(locator, code, offset)
    }
}

impl Locate for syn::ExprClosure {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        (
            &self.attrs,
            &self.lifetimes,
            &self.constness,
            &self.movability,
            &self.asyncness,
            &self.capture,
            &self.or1_token,
            &self.inputs,
            &self.or2_token,
            &self.output,
            &self.body,
        )
            .locate_as_group(locator, code, offset)
    }
}

impl Locate for syn::ExprConst {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        (&self.attrs, &self.const_token, &self.block).locate_as_group(locator, code, offset)
    }
}

impl Locate for syn::ExprContinue {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        (&self.attrs, &self.continue_token, &self.label).locate_as_group(locator, code, offset)
    }
}

impl Locate for syn::ExprField {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        (&self.attrs, &self.base, &self.dot_token, &self.member)
            .locate_as_group(locator, code, offset)
    }
}

impl Locate for syn::ExprForLoop {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        (
            &self.attrs,
            &self.label,
            &self.for_token,
            &self.pat,
            &self.in_token,
            &self.expr,
            &self.body,
        )
            .locate_as_group(locator, code, offset)
    }
}

impl Locate for syn::ExprGroup {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        (&self.attrs, &self.group_token, &self.expr).locate_as_group(locator, code, offset)
    }
}

impl Locate for syn::ExprIf {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        if let Some((else_token, else_branch)) = &self.else_branch {
            (
                &self.attrs,
                &self.if_token,
                &self.cond,
                &self.then_branch,
                else_token,
                else_branch,
            )
                .locate_as_group(locator, code, offset)
        } else {
            (&self.attrs, &self.if_token, &self.cond, &self.then_branch)
                .locate_as_group(locator, code, offset)
        }
    }
}

impl Locate for syn::ExprIndex {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        Surround {
            front: (&self.attrs, &self.expr),
            surround: &self.bracket_token,
            inner: &self.index,
            back: (),
        }
        .locate(locator, code, offset)
    }
}

impl Locate for syn::ExprInfer {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        (&self.attrs, &self.underscore_token).locate_as_group(locator, code, offset)
    }
}

impl Locate for syn::ExprLet {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        (
            &self.attrs,
            &self.let_token,
            &self.pat,
            &self.eq_token,
            &self.expr,
        )
            .locate_as_group(locator, code, offset)
    }
}

impl Locate for syn::ExprLit {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        (&self.attrs, &self.lit).locate_as_group(locator, code, offset)
    }
}

impl Locate for syn::ExprLoop {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        (&self.attrs, &self.label, &self.loop_token, &self.body)
            .locate_as_group(locator, code, offset)
    }
}

impl Locate for syn::ExprMacro {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        (&self.attrs, &self.mac).locate_as_group(locator, code, offset)
    }
}

impl Locate for syn::ExprMatch {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        Surround {
            front: (&self.attrs, &self.match_token, &self.expr),
            surround: &self.brace_token,
            inner: &self.arms,
            back: (),
        }
        .locate(locator, code, offset)
    }
}

impl Locate for syn::ExprMethodCall {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        Surround {
            front: (
                &self.attrs,
                &self.receiver,
                &self.dot_token,
                &self.method,
                &self.turbofish,
            ),
            surround: &self.paren_token,
            inner: &self.args,
            back: (),
        }
        .locate(locator, code, offset)
    }
}

impl Locate for syn::ExprParen {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        Surround {
            front: &self.attrs,
            surround: &self.paren_token,
            inner: &self.expr,
            back: (),
        }
        .locate(locator, code, offset)
    }
}

impl Locate for syn::ExprPath {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        if let Some(qself) = &self.qself {
            Qualified {
                front: &self.attrs,
                qself,
                path: &self.path,
                back: (),
            }
            .locate(locator, code, offset)
        } else {
            (&self.attrs, &self.path).locate_as_group(locator, code, offset)
        }
    }
}

impl Locate for syn::ExprRange {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        match (&self.start, &self.end) {
            (Some(start), Some(end)) => {
                (&self.attrs, start, &self.limits, end).locate_as_group(locator, code, offset)
            }
            (Some(start), None) => {
                (&self.attrs, start, &self.limits).locate_as_group(locator, code, offset)
            }
            (None, Some(end)) => {
                (&self.attrs, &self.limits, end).locate_as_group(locator, code, offset)
            }
            (None, None) => (&self.attrs, &self.limits).locate_as_group(locator, code, offset),
        }
    }
}

impl Locate for syn::ExprRawAddr {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        (
            &self.attrs,
            &self.and_token,
            &self.raw,
            &self.mutability,
            &self.expr,
        )
            .locate_as_group(locator, code, offset)
    }
}

impl Locate for syn::ExprReference {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        (&self.attrs, &self.and_token, &self.mutability, &self.expr)
            .locate_as_group(locator, code, offset)
    }
}

impl Locate for syn::ExprRepeat {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        Surround {
            front: &self.attrs,
            surround: &self.bracket_token,
            inner: (&self.expr, &self.semi_token, &self.len),
            back: (),
        }
        .locate(locator, code, offset)
    }
}

impl Locate for syn::ExprReturn {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        (&self.attrs, &self.return_token, &self.expr).locate_as_group(locator, code, offset)
    }
}

impl Locate for syn::ExprStruct {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        let front_loc = if let Some(qself) = &self.qself {
            Qualified {
                front: &self.attrs,
                qself,
                path: &self.path,
                back: (),
            }
            .locate(locator, code, offset)
        } else {
            (&self.attrs, &self.path).locate_as_group(locator, code, offset)
        };

        let back_loc = Surround {
            front: (),
            surround: &self.brace_token,
            inner: (&self.fields, &self.dot2_token, &self.rest),
            back: (),
        }
        .locate(locator, code, front_loc.end);

        Location {
            start: front_loc.start,
            end: back_loc.end,
        }
    }
}

impl Locate for syn::ExprTry {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        (&self.attrs, &self.expr, &self.question_token).locate_as_group(locator, code, offset)
    }
}

impl Locate for syn::ExprTryBlock {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        (&self.attrs, &self.try_token, &self.block).locate_as_group(locator, code, offset)
    }
}

impl Locate for syn::ExprTuple {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        Surround {
            front: &self.attrs,
            surround: &self.paren_token,
            inner: &self.elems,
            back: (),
        }
        .locate(locator, code, offset)
    }
}

impl Locate for syn::ExprUnary {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        (&self.attrs, &self.op, &self.expr).locate_as_group(locator, code, offset)
    }
}

impl Locate for syn::ExprUnsafe {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        (&self.attrs, &self.unsafe_token, &self.block).locate_as_group(locator, code, offset)
    }
}

impl Locate for syn::ExprWhile {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        (
            &self.attrs,
            &self.label,
            &self.while_token,
            &self.cond,
            &self.body,
        )
            .locate_as_group(locator, code, offset)
    }
}

impl Locate for syn::ExprYield {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        (&self.attrs, &self.yield_token, &self.expr).locate_as_group(locator, code, offset)
    }
}

impl Locate for syn::Field {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        (
            &self.attrs,
            &self.vis,
            &self.mutability,
            &self.ident,
            &self.colon_token,
            &self.ty,
        )
            .locate_as_group(locator, code, offset)
    }
}

impl Locate for syn::FieldMutability {
    fn find_loc(&self, _locator: &mut Locator, _code: &str, offset: usize) -> Location {
        Location {
            start: offset,
            end: offset,
        }
    }
}

// When a field pattern has no colon, syn parses `member` from the token stream and clones `pat`
// from `member`, so `pat` does not have its own source span.
// ref: https://github.com/dtolnay/syn/blob/5357c8fb6bd29fd7c829e0aede1dab4b45a6e00f/src/pat.rs#L562-L594
impl Locate for syn::FieldPat {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        if self.colon_token.is_some() || !matches!(self.member, syn::Member::Named(_)) {
            (&self.attrs, &self.member, &self.colon_token, &self.pat)
                .locate_as_group(locator, code, offset)
        } else {
            let loc =
                (&self.attrs, &self.colon_token, &self.pat).locate_as_group(locator, code, offset);
            self.member
                .locate(locator, code, self.attrs._location(locator).end);
            loc
        }
    }
}

impl Locate for syn::Fields {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        match self {
            Self::Named(v) => v.locate(locator, code, offset),
            Self::Unnamed(v) => v.locate(locator, code, offset),
            Self::Unit => Location {
                start: offset,
                end: offset,
            },
        }
    }
}

impl Locate for syn::FieldsNamed {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        Surround {
            front: (),
            surround: &self.brace_token,
            inner: &self.named,
            back: (),
        }
        .locate(locator, code, offset)
    }
}

impl Locate for syn::FieldsUnnamed {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        Surround {
            front: (),
            surround: &self.paren_token,
            inner: &self.unnamed,
            back: (),
        }
        .locate(locator, code, offset)
    }
}

// When a field value has no colon, syn parses `member` from the token stream and clones `expr`
// from `member`, so `expr` does not have its own source span.
// ref: https://github.com/dtolnay/syn/blob/5357c8fb6bd29fd7c829e0aede1dab4b45a6e00f/src/expr.rs#L2744-L2755
impl Locate for syn::FieldValue {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        if self.colon_token.is_some() || !matches!(self.member, syn::Member::Named(_)) {
            (&self.attrs, &self.member, &self.colon_token, &self.expr)
                .locate_as_group(locator, code, offset)
        } else {
            let loc = (&self.attrs, &self.member, &self.colon_token)
                .locate_as_group(locator, code, offset);
            self.expr
                .locate(locator, code, self.attrs._location(locator).end);
            loc
        }
    }
}

impl Locate for syn::File {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        (&self.attrs, &self.items).locate_as_group(locator, code, offset)
    }
}

impl Locate for syn::FnArg {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        match self {
            Self::Receiver(v) => v.locate(locator, code, offset),
            Self::Typed(v) => v.locate(locator, code, offset),
        }
    }
}

impl Locate for syn::ForeignItem {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        match self {
            Self::Fn(v) => v.locate(locator, code, offset),
            Self::Static(v) => v.locate(locator, code, offset),
            Self::Type(v) => v.locate(locator, code, offset),
            Self::Macro(v) => v.locate(locator, code, offset),
            Self::Verbatim(_) => Location {
                start: offset,
                end: offset,
            },
            _ => Location {
                start: offset,
                end: offset,
            },
        }
    }
}

impl Locate for syn::ForeignItemFn {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        (&self.attrs, &self.vis, &self.sig, &self.semi_token).locate_as_group(locator, code, offset)
    }
}

impl Locate for syn::ForeignItemStatic {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        (
            &self.attrs,
            &self.vis,
            &self.static_token,
            &self.mutability,
            &self.ident,
            &self.colon_token,
            &self.ty,
            &self.semi_token,
        )
            .locate_as_group(locator, code, offset)
    }
}

impl Locate for syn::ForeignItemType {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        (
            &self.attrs,
            &self.vis,
            &self.type_token,
            &self.ident,
            &self.generics,
            &self.semi_token,
        )
            .locate_as_group(locator, code, offset)
    }
}

impl Locate for syn::ForeignItemMacro {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        (&self.attrs, &self.mac, &self.semi_token).locate_as_group(locator, code, offset)
    }
}

impl Locate for syn::GenericArgument {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        match self {
            Self::Lifetime(v) => v.locate(locator, code, offset),
            Self::Type(v) => v.locate(locator, code, offset),
            Self::Const(v) => v.locate(locator, code, offset),
            Self::AssocType(v) => v.locate(locator, code, offset),
            Self::AssocConst(v) => v.locate(locator, code, offset),
            Self::Constraint(v) => v.locate(locator, code, offset),
            _ => Location {
                start: offset,
                end: offset,
            },
        }
    }
}

impl Locate for syn::GenericParam {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        match self {
            Self::Lifetime(v) => v.locate(locator, code, offset),
            Self::Type(v) => v.locate(locator, code, offset),
            Self::Const(v) => v.locate(locator, code, offset),
        }
    }
}

impl Locate for syn::Generics {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        (
            &self.lt_token,
            &self.params,
            &self.gt_token,
            &self.where_clause,
        )
            .locate_as_group(locator, code, offset)
    }
}

impl Locate for syn::Ident {
    fn find_loc(&self, _locator: &mut Locator, code: &str, offset: usize) -> Location {
        let cur_code = &code[offset..];

        let ident = self.to_string();
        let start = offset
            + cur_code
                .find(&ident)
                .unwrap_or_else(|| panic!("expected `{ident}` from `{cur_code}`"));

        Location {
            start,
            end: start + ident.len(),
        }
    }
}

impl Locate for syn::ImplItem {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        match self {
            Self::Const(v) => v.locate(locator, code, offset),
            Self::Fn(v) => v.locate(locator, code, offset),
            Self::Type(v) => v.locate(locator, code, offset),
            Self::Macro(v) => v.locate(locator, code, offset),
            Self::Verbatim(_) => Location {
                start: offset,
                end: offset,
            },
            _ => Location {
                start: offset,
                end: offset,
            },
        }
    }
}

impl Locate for syn::ImplItemConst {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        (
            &self.attrs,
            &self.vis,
            &self.defaultness,
            &self.const_token,
            &self.ident,
            &self.generics,
            &self.colon_token,
            &self.ty,
            &self.eq_token,
            &self.expr,
            &self.semi_token,
        )
            .locate_as_group(locator, code, offset)
    }
}

impl Locate for syn::ImplItemFn {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        (
            &self.attrs,
            &self.vis,
            &self.defaultness,
            &self.sig,
            &self.block,
        )
            .locate_as_group(locator, code, offset)
    }
}

impl Locate for syn::ImplItemType {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        (
            &self.attrs,
            &self.vis,
            &self.defaultness,
            &self.type_token,
            &self.ident,
            &self.generics,
            &self.eq_token,
            &self.ty,
            &self.semi_token,
        )
            .locate_as_group(locator, code, offset)
    }
}

impl Locate for syn::ImplItemMacro {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        (&self.attrs, &self.mac, &self.semi_token).locate_as_group(locator, code, offset)
    }
}

impl Locate for syn::ImplRestriction {
    fn find_loc(&self, _locator: &mut Locator, _code: &str, offset: usize) -> Location {
        Location {
            start: offset,
            end: offset,
        }
    }
}

impl Locate for syn::Index {
    fn find_loc(&self, _locator: &mut Locator, code: &str, offset: usize) -> Location {
        let value = self.index.to_string();
        helper::str_location(code, offset, &value)
    }
}

impl Locate for syn::Item {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        match self {
            Self::Const(v) => v.locate(locator, code, offset),
            Self::Enum(v) => v.locate(locator, code, offset),
            Self::ExternCrate(v) => v.locate(locator, code, offset),
            Self::Fn(v) => v.locate(locator, code, offset),
            Self::ForeignMod(v) => v.locate(locator, code, offset),
            Self::Impl(v) => v.locate(locator, code, offset),
            Self::Macro(v) => v.locate(locator, code, offset),
            Self::Mod(v) => v.locate(locator, code, offset),
            Self::Static(v) => v.locate(locator, code, offset),
            Self::Struct(v) => v.locate(locator, code, offset),
            Self::Trait(v) => v.locate(locator, code, offset),
            Self::TraitAlias(v) => v.locate(locator, code, offset),
            Self::Type(v) => v.locate(locator, code, offset),
            Self::Union(v) => v.locate(locator, code, offset),
            Self::Use(v) => v.locate(locator, code, offset),
            Self::Verbatim(_) => Location {
                start: offset,
                end: offset,
            },
            _ => Location {
                start: offset,
                end: offset,
            },
        }
    }
}

impl Locate for syn::ItemConst {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        (
            &self.attrs,
            &self.vis,
            &self.const_token,
            &self.ident,
            &self.generics,
            &self.colon_token,
            &self.ty,
            &self.eq_token,
            &self.expr,
            &self.semi_token,
        )
            .locate_as_group(locator, code, offset)
    }
}

impl Locate for syn::ItemEnum {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        Surround {
            front: (
                &self.attrs,
                &self.vis,
                &self.enum_token,
                &self.ident,
                &self.generics,
            ),
            surround: &self.brace_token,
            inner: &self.variants,
            back: (),
        }
        .locate(locator, code, offset)
    }
}

impl Locate for syn::ItemExternCrate {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        if let Some((as_token, rename)) = &self.rename {
            (
                &self.attrs,
                &self.vis,
                &self.extern_token,
                &self.crate_token,
                &self.ident,
                as_token,
                rename,
                &self.semi_token,
            )
                .locate_as_group(locator, code, offset)
        } else {
            (
                &self.attrs,
                &self.vis,
                &self.extern_token,
                &self.crate_token,
                &self.ident,
                &self.semi_token,
            )
                .locate_as_group(locator, code, offset)
        }
    }
}

impl Locate for syn::ItemFn {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        (&self.attrs, &self.vis, &self.sig, &self.block).locate_as_group(locator, code, offset)
    }
}

impl Locate for syn::ItemForeignMod {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        Surround {
            front: (&self.attrs, &self.unsafety, &self.abi),
            surround: &self.brace_token,
            inner: &self.items,
            back: (),
        }
        .locate(locator, code, offset)
    }
}

impl Locate for syn::ItemImpl {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        let loc = if let Some((exc_token, path, for_token)) = &self.trait_ {
            Surround {
                front: (
                    &self.attrs,
                    &self.defaultness,
                    &self.unsafety,
                    &self.impl_token,
                    // The `where` clause follows `self.self_ty`.
                    &self.generics.lt_token,
                    &self.generics.params,
                    &self.generics.gt_token,
                    exc_token,
                    path,
                    for_token,
                    &self.self_ty,
                    &self.generics.where_clause,
                ),
                surround: &self.brace_token,
                inner: &self.items,
                back: (),
            }
            .locate(locator, code, offset)
        } else {
            Surround {
                front: (
                    &self.attrs,
                    &self.defaultness,
                    &self.unsafety,
                    &self.impl_token,
                    // The `where` clause follows `self.self_ty`.
                    &self.generics.lt_token,
                    &self.generics.params,
                    &self.generics.gt_token,
                    &self.self_ty,
                    &self.generics.where_clause,
                ),
                surround: &self.brace_token,
                inner: &self.items,
                back: (),
            }
            .locate(locator, code, offset)
        };

        locate_generics(locator, &self.generics);
        loc
    }
}

// syn parses these fields in a different order from their struct declaration.
// ref: https://github.com/dtolnay/syn/blob/5357c8fb6bd29fd7c829e0aede1dab4b45a6e00f/src/item.rs#L1240
impl Locate for syn::ItemMacro {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        Surround {
            front: (
                &self.attrs,
                &self.mac.path,
                &self.mac.bang_token,
                &self.ident,
            ),
            surround: &self.mac.delimiter,
            inner: (), // Macro tokens are not processed yet.
            back: &self.semi_token,
        }
        .locate(locator, code, offset)
    }
}

impl Locate for syn::ItemMod {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        match (&self.content, &self.semi) {
            (Some((brace, items)), Some(semi_token)) => Surround {
                front: (&self.attrs, &self.vis, &self.mod_token, &self.ident),
                surround: brace,
                inner: items,
                back: semi_token,
            }
            .locate(locator, code, offset),
            (Some((brace, items)), None) => Surround {
                front: (&self.attrs, &self.vis, &self.mod_token, &self.ident),
                surround: brace,
                inner: items,
                back: (),
            }
            .locate(locator, code, offset),
            (None, Some(semi_token)) => (
                &self.attrs,
                &self.vis,
                &self.mod_token,
                &self.ident,
                semi_token,
            )
                .locate_as_group(locator, code, offset),
            (None, None) => (&self.attrs, &self.vis, &self.mod_token, &self.ident)
                .locate_as_group(locator, code, offset),
        }
    }
}

impl Locate for syn::ItemStatic {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        (
            &self.attrs,
            &self.vis,
            &self.static_token,
            &self.mutability,
            &self.ident,
            &self.colon_token,
            &self.ty,
            &self.eq_token,
            &self.expr,
            &self.semi_token,
        )
            .locate_as_group(locator, code, offset)
    }
}

impl Locate for syn::ItemStruct {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        (
            &self.attrs,
            &self.vis,
            &self.struct_token,
            &self.ident,
            &self.generics,
            &self.fields,
            &self.semi_token,
        )
            .locate_as_group(locator, code, offset)
    }
}

impl Locate for syn::ItemTrait {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        Surround {
            front: (
                &self.attrs,
                &self.vis,
                &self.unsafety,
                &self.auto_token,
                &self.restriction,
                &self.trait_token,
                &self.ident,
                &self.generics,
                &self.colon_token,
                &self.supertraits,
            ),
            surround: &self.brace_token,
            inner: &self.items,
            back: (),
        }
        .locate(locator, code, offset)
    }
}

impl Locate for syn::ItemTraitAlias {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        (
            &self.attrs,
            &self.vis,
            &self.trait_token,
            &self.ident,
            &self.generics,
            &self.eq_token,
            &self.bounds,
            &self.semi_token,
        )
            .locate_as_group(locator, code, offset)
    }
}

impl Locate for syn::ItemType {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        (
            &self.attrs,
            &self.vis,
            &self.type_token,
            &self.ident,
            &self.generics,
            &self.eq_token,
            &self.ty,
            &self.semi_token,
        )
            .locate_as_group(locator, code, offset)
    }
}

impl Locate for syn::ItemUnion {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        (
            &self.attrs,
            &self.vis,
            &self.union_token,
            &self.ident,
            &self.generics,
            &self.fields,
        )
            .locate_as_group(locator, code, offset)
    }
}

impl Locate for syn::ItemUse {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        (
            &self.attrs,
            &self.vis,
            &self.use_token,
            &self.leading_colon,
            &self.tree,
            &self.semi_token,
        )
            .locate_as_group(locator, code, offset)
    }
}

impl Locate for syn::Label {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        (&self.name, &self.colon_token).locate_as_group(locator, code, offset)
    }
}

impl Locate for syn::Lifetime {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        let cur_code = &code[offset..];

        let start = offset
            + cur_code
                .find('\'')
                .unwrap_or_else(|| panic!("expected ' from {cur_code}"));
        let end = self.ident.locate(locator, code, start + 1).end;

        Location { start, end }
    }
}

impl Locate for syn::LifetimeParam {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        (&self.attrs, &self.lifetime, &self.colon_token, &self.bounds)
            .locate_as_group(locator, code, offset)
    }
}

impl Locate for syn::Lit {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        match self {
            Self::Str(v) => v.locate(locator, code, offset),
            Self::ByteStr(v) => v.locate(locator, code, offset),
            Self::CStr(v) => v.locate(locator, code, offset),
            Self::Byte(v) => v.locate(locator, code, offset),
            Self::Char(v) => v.locate(locator, code, offset),
            Self::Int(v) => v.locate(locator, code, offset),
            Self::Float(v) => v.locate(locator, code, offset),
            Self::Bool(v) => v.locate(locator, code, offset),
            Self::Verbatim(_) => Location {
                start: offset,
                end: offset,
            },
            _ => Location {
                start: offset,
                end: offset,
            },
        }
    }
}

impl Locate for syn::LitStr {
    fn find_loc(&self, _locator: &mut Locator, code: &str, offset: usize) -> Location {
        let lit = self.token().to_string();
        helper::str_location(code, offset, &lit)
    }
}

impl Locate for syn::LitByteStr {
    fn find_loc(&self, _locator: &mut Locator, code: &str, offset: usize) -> Location {
        let lit = self.token().to_string();
        helper::str_location(code, offset, &lit)
    }
}

impl Locate for syn::LitCStr {
    fn find_loc(&self, _locator: &mut Locator, code: &str, offset: usize) -> Location {
        let lit = self.token().to_string();
        helper::str_location(code, offset, &lit)
    }
}

impl Locate for syn::LitByte {
    fn find_loc(&self, _locator: &mut Locator, code: &str, offset: usize) -> Location {
        let lit = self.token().to_string();
        helper::str_location(code, offset, &lit)
    }
}

impl Locate for syn::LitChar {
    fn find_loc(&self, _locator: &mut Locator, code: &str, offset: usize) -> Location {
        let lit = self.token().to_string();
        helper::str_location(code, offset, &lit)
    }
}

impl Locate for syn::LitInt {
    fn find_loc(&self, _locator: &mut Locator, code: &str, offset: usize) -> Location {
        let lit = self.token().to_string();
        helper::str_location(code, offset, &lit)
    }
}

impl Locate for syn::LitFloat {
    fn find_loc(&self, _locator: &mut Locator, code: &str, offset: usize) -> Location {
        let lit = self.token().to_string();
        helper::str_location(code, offset, &lit)
    }
}

impl Locate for syn::LitBool {
    fn find_loc(&self, _locator: &mut Locator, code: &str, offset: usize) -> Location {
        let lit = self.token().to_string();
        helper::str_location(code, offset, &lit)
    }
}

impl Locate for syn::Local {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        (
            &self.attrs,
            &self.let_token,
            &self.pat,
            &self.init,
            &self.semi_token,
        )
            .locate_as_group(locator, code, offset)
    }
}

impl Locate for syn::LocalInit {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        if let Some((else_token, diverge)) = &self.diverge {
            (&self.eq_token, &self.expr, else_token, diverge).locate_as_group(locator, code, offset)
        } else {
            (&self.eq_token, &self.expr).locate_as_group(locator, code, offset)
        }
    }
}

impl Locate for syn::Macro {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        match &self.delimiter {
            syn::MacroDelimiter::Paren(paren) => Surround {
                front: (&self.path, &self.bang_token),
                surround: paren,
                inner: (),
                back: (),
            }
            .locate(locator, code, offset),
            syn::MacroDelimiter::Brace(brace) => Surround {
                front: (&self.path, &self.bang_token),
                surround: brace,
                inner: (),
                back: (),
            }
            .locate(locator, code, offset),
            syn::MacroDelimiter::Bracket(bracket) => Surround {
                front: (&self.path, &self.bang_token),
                surround: bracket,
                inner: (),
                back: (),
            }
            .locate(locator, code, offset),
        }
    }
}

impl Locate for syn::MacroDelimiter {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        match self {
            Self::Paren(v) => v.locate(locator, code, offset),
            Self::Brace(v) => v.locate(locator, code, offset),
            Self::Bracket(v) => v.locate(locator, code, offset),
        }
    }
}

impl Locate for syn::Member {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        match self {
            Self::Named(v) => v.locate(locator, code, offset),
            Self::Unnamed(v) => v.locate(locator, code, offset),
        }
    }
}

impl Locate for syn::Meta {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        match self {
            Self::Path(v) => v.locate(locator, code, offset),
            Self::List(v) => v.locate(locator, code, offset),
            Self::NameValue(v) => v.locate(locator, code, offset),
        }
    }
}

impl Locate for syn::MetaList {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        match &self.delimiter {
            syn::MacroDelimiter::Paren(paren) => Surround {
                front: &self.path,
                surround: paren,
                inner: (),
                back: (),
            }
            .locate(locator, code, offset),
            syn::MacroDelimiter::Brace(brace) => Surround {
                front: &self.path,
                surround: brace,
                inner: (),
                back: (),
            }
            .locate(locator, code, offset),
            syn::MacroDelimiter::Bracket(bracket) => Surround {
                front: &self.path,
                surround: bracket,
                inner: (),
                back: (),
            }
            .locate(locator, code, offset),
        }
    }
}

impl Locate for syn::MetaNameValue {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        (&self.path, &self.eq_token, &self.value).locate_as_group(locator, code, offset)
    }
}

impl Locate for syn::ParenthesizedGenericArguments {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        Surround {
            front: (),
            surround: &self.paren_token,
            inner: &self.inputs,
            back: &self.output,
        }
        .locate(locator, code, offset)
    }
}

impl Locate for syn::Pat {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        match self {
            Self::Const(v) => v.locate(locator, code, offset),
            Self::Ident(v) => v.locate(locator, code, offset),
            Self::Lit(v) => v.locate(locator, code, offset),
            Self::Macro(v) => v.locate(locator, code, offset),
            Self::Or(v) => v.locate(locator, code, offset),
            Self::Paren(v) => v.locate(locator, code, offset),
            Self::Path(v) => v.locate(locator, code, offset),
            Self::Range(v) => v.locate(locator, code, offset),
            Self::Reference(v) => v.locate(locator, code, offset),
            Self::Rest(v) => v.locate(locator, code, offset),
            Self::Slice(v) => v.locate(locator, code, offset),
            Self::Struct(v) => v.locate(locator, code, offset),
            Self::Tuple(v) => v.locate(locator, code, offset),
            Self::TupleStruct(v) => v.locate(locator, code, offset),
            Self::Type(v) => v.locate(locator, code, offset),
            Self::Verbatim(_) => Location {
                start: offset,
                end: offset,
            },
            Self::Wild(v) => v.locate(locator, code, offset),
            _ => Location {
                start: offset,
                end: offset,
            },
        }
    }
}

impl Locate for syn::PatIdent {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        if let Some((at_token, subpat)) = &self.subpat {
            (
                &self.attrs,
                &self.by_ref,
                &self.mutability,
                &self.ident,
                at_token,
                subpat,
            )
                .locate_as_group(locator, code, offset)
        } else {
            (&self.attrs, &self.by_ref, &self.mutability, &self.ident)
                .locate_as_group(locator, code, offset)
        }
    }
}

impl Locate for syn::PatOr {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        (&self.attrs, &self.leading_vert, &self.cases).locate_as_group(locator, code, offset)
    }
}

impl Locate for syn::PatParen {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        Surround {
            front: &self.attrs,
            surround: &self.paren_token,
            inner: &self.pat,
            back: (),
        }
        .locate(locator, code, offset)
    }
}

impl Locate for syn::PatReference {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        (&self.attrs, &self.and_token, &self.mutability, &self.pat)
            .locate_as_group(locator, code, offset)
    }
}

impl Locate for syn::PatRest {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        (&self.attrs, &self.dot2_token).locate_as_group(locator, code, offset)
    }
}

impl Locate for syn::PatSlice {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        Surround {
            front: &self.attrs,
            surround: &self.bracket_token,
            inner: &self.elems,
            back: (),
        }
        .locate(locator, code, offset)
    }
}

impl Locate for syn::PatStruct {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        let front_loc = if let Some(qself) = &self.qself {
            Qualified {
                front: &self.attrs,
                qself,
                path: &self.path,
                back: (),
            }
            .locate(locator, code, offset)
        } else {
            (&self.attrs, &self.path).locate_as_group(locator, code, offset)
        };

        let back_loc = Surround {
            front: (),
            surround: &self.brace_token,
            inner: (&self.fields, &self.rest),
            back: (),
        }
        .locate(locator, code, front_loc.end);

        Location {
            start: front_loc.start,
            end: back_loc.end,
        }
    }
}

impl Locate for syn::PatTuple {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        Surround {
            front: &self.attrs,
            surround: &self.paren_token,
            inner: &self.elems,
            back: (),
        }
        .locate(locator, code, offset)
    }
}

impl Locate for syn::PatTupleStruct {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        let front_loc = if let Some(qself) = &self.qself {
            Qualified {
                front: &self.attrs,
                qself,
                path: &self.path,
                back: (),
            }
            .locate(locator, code, offset)
        } else {
            (&self.attrs, &self.path).locate_as_group(locator, code, offset)
        };

        let back_loc = Surround {
            front: (),
            surround: &self.paren_token,
            inner: &self.elems,
            back: (),
        }
        .locate(locator, code, front_loc.end);

        Location {
            start: front_loc.start,
            end: back_loc.end,
        }
    }
}

impl Locate for syn::PatType {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        (&self.attrs, &self.pat, &self.colon_token, &self.ty).locate_as_group(locator, code, offset)
    }
}

impl Locate for syn::PatWild {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        (&self.attrs, &self.underscore_token).locate_as_group(locator, code, offset)
    }
}

impl Locate for syn::Path {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        (&self.leading_colon, &self.segments).locate_as_group(locator, code, offset)
    }
}

impl Locate for syn::PathArguments {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        match self {
            Self::None => Location {
                start: offset,
                end: offset,
            },
            Self::AngleBracketed(v) => v.locate(locator, code, offset),
            Self::Parenthesized(v) => v.locate(locator, code, offset),
        }
    }
}

impl Locate for syn::PathSegment {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        (&self.ident, &self.arguments).locate_as_group(locator, code, offset)
    }
}

impl Locate for syn::PointerMutability {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        match self {
            Self::Const(v) => v.locate(locator, code, offset),
            Self::Mut(v) => v.locate(locator, code, offset),
        }
    }
}

impl Locate for syn::PreciseCapture {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        (
            &self.use_token,
            &self.lt_token,
            &self.params,
            &self.gt_token,
        )
            .locate_as_group(locator, code, offset)
    }
}

impl Locate for syn::PredicateLifetime {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        (&self.lifetime, &self.colon_token, &self.bounds).locate_as_group(locator, code, offset)
    }
}

impl Locate for syn::PredicateType {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        (
            &self.lifetimes,
            &self.bounded_ty,
            &self.colon_token,
            &self.bounds,
        )
            .locate_as_group(locator, code, offset)
    }
}

impl Locate for syn::QSelf {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        let front_loc =
            (&self.lt_token, &self.ty, &self.as_token).locate_as_group(locator, code, offset);

        const OPEN: char = '<';
        const CLOSE: char = '>';

        let cur_code = &code[front_loc.end..];

        let mut cur = front_loc.end;
        let mut level = 1;

        for c in cur_code.chars() {
            if c == OPEN {
                level += 1;
            } else if c == CLOSE {
                if level == 1 {
                    break;
                }
                level -= 1;
            }
            cur += c.len_utf8();
        }

        let end = self.gt_token.locate(locator, code, cur).end;

        Location {
            start: front_loc.start,
            end,
        }
    }
}

impl Locate for syn::RangeLimits {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        match self {
            Self::HalfOpen(v) => v.locate(locator, code, offset),
            Self::Closed(v) => v.locate(locator, code, offset),
        }
    }
}

impl Locate for syn::Receiver {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        // Without an explicit receiver type (`self: Type`), syn synthesizes `self.ty`.

        if let Some((and_token, reference)) = &self.reference {
            if let Some(colon_token) = &self.colon_token {
                (
                    &self.attrs,
                    and_token,
                    reference,
                    &self.mutability,
                    &self.self_token,
                    colon_token,
                    &self.ty,
                )
                    .locate_as_group(locator, code, offset)
            } else {
                (
                    &self.attrs,
                    and_token,
                    reference,
                    &self.mutability,
                    &self.self_token,
                )
                    .locate_as_group(locator, code, offset)
            }
        } else if let Some(colon_token) = &self.colon_token {
            (
                &self.attrs,
                &self.mutability,
                &self.self_token,
                colon_token,
                &self.ty,
            )
                .locate_as_group(locator, code, offset)
        } else {
            (&self.attrs, &self.mutability, &self.self_token).locate_as_group(locator, code, offset)
        }
    }
}

impl Locate for syn::ReturnType {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        match self {
            Self::Default => Location {
                start: offset,
                end: offset,
            },
            Self::Type(arrow_token, ty) => (arrow_token, ty).locate_as_group(locator, code, offset),
        }
    }
}

impl Locate for syn::Signature {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        let loc = Surround {
            front: (
                &self.constness,
                &self.asyncness,
                &self.unsafety,
                &self.abi,
                &self.fn_token,
                &self.ident,
                // The `where` clause follows the return type.
                &self.generics.lt_token,
                &self.generics.params,
                &self.generics.gt_token,
            ),
            surround: &self.paren_token,
            inner: (&self.inputs, &self.variadic),
            back: (&self.output, &self.generics.where_clause),
        }
        .locate(locator, code, offset);

        locate_generics(locator, &self.generics);
        loc
    }
}

impl Locate for syn::StaticMutability {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        match self {
            Self::Mut(v) => v.locate(locator, code, offset),
            Self::None => Location {
                start: offset,
                end: offset,
            },
            _ => Location {
                start: offset,
                end: offset,
            },
        }
    }
}

impl Locate for syn::Stmt {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        match self {
            Self::Local(v) => v.locate(locator, code, offset),
            Self::Item(v) => v.locate(locator, code, offset),
            Self::Expr(expr, semi_token) => {
                (expr, semi_token).locate_as_group(locator, code, offset)
            }
            Self::Macro(v) => v.locate(locator, code, offset),
        }
    }
}

impl Locate for syn::StmtMacro {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        (&self.attrs, &self.mac, &self.semi_token).locate_as_group(locator, code, offset)
    }
}

impl Locate for syn::TraitBound {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        // syn always parses this paren token as empty.
        (&self.modifier, &self.lifetimes, &self.path).locate_as_group(locator, code, offset)
    }
}

impl Locate for syn::TraitBoundModifier {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        match self {
            Self::None => Location {
                start: offset,
                end: offset,
            },
            Self::Maybe(v) => v.locate(locator, code, offset),
        }
    }
}

impl Locate for syn::TraitItem {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        match self {
            Self::Const(v) => v.locate(locator, code, offset),
            Self::Fn(v) => v.locate(locator, code, offset),
            Self::Type(v) => v.locate(locator, code, offset),
            Self::Macro(v) => v.locate(locator, code, offset),
            Self::Verbatim(_) => Location {
                start: offset,
                end: offset,
            },
            _ => Location {
                start: offset,
                end: offset,
            },
        }
    }
}

impl Locate for syn::TraitItemConst {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        if let Some((eq_token, default)) = &self.default {
            (
                &self.attrs,
                &self.const_token,
                &self.ident,
                &self.generics,
                &self.colon_token,
                &self.ty,
                eq_token,
                default,
                &self.semi_token,
            )
                .locate_as_group(locator, code, offset)
        } else {
            (
                &self.attrs,
                &self.const_token,
                &self.ident,
                &self.generics,
                &self.colon_token,
                &self.ty,
                &self.semi_token,
            )
                .locate_as_group(locator, code, offset)
        }
    }
}

impl Locate for syn::TraitItemFn {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        (&self.attrs, &self.sig, &self.default, &self.semi_token)
            .locate_as_group(locator, code, offset)
    }
}

impl Locate for syn::TraitItemType {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        if let Some((eq_token, default)) = &self.default {
            (
                &self.attrs,
                &self.type_token,
                &self.ident,
                &self.generics,
                &self.colon_token,
                &self.bounds,
                eq_token,
                default,
                &self.semi_token,
            )
                .locate_as_group(locator, code, offset)
        } else {
            (
                &self.attrs,
                &self.type_token,
                &self.ident,
                &self.generics,
                &self.colon_token,
                &self.bounds,
                &self.semi_token,
            )
                .locate_as_group(locator, code, offset)
        }
    }
}

impl Locate for syn::TraitItemMacro {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        (&self.attrs, &self.mac, &self.semi_token).locate_as_group(locator, code, offset)
    }
}

impl Locate for syn::Type {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        match self {
            Self::Array(v) => v.locate(locator, code, offset),
            Self::BareFn(v) => v.locate(locator, code, offset),
            Self::Group(v) => v.locate(locator, code, offset),
            Self::ImplTrait(v) => v.locate(locator, code, offset),
            Self::Infer(v) => v.locate(locator, code, offset),
            Self::Macro(v) => v.locate(locator, code, offset),
            Self::Never(v) => v.locate(locator, code, offset),
            Self::Paren(v) => v.locate(locator, code, offset),
            Self::Path(v) => v.locate(locator, code, offset),
            Self::Ptr(v) => v.locate(locator, code, offset),
            Self::Reference(v) => v.locate(locator, code, offset),
            Self::Slice(v) => v.locate(locator, code, offset),
            Self::TraitObject(v) => v.locate(locator, code, offset),
            Self::Tuple(v) => v.locate(locator, code, offset),
            Self::Verbatim(_) => Location {
                start: offset,
                end: offset,
            },
            _ => Location {
                start: offset,
                end: offset,
            },
        }
    }
}

impl Locate for syn::TypeArray {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        Surround {
            front: (),
            surround: &self.bracket_token,
            inner: (&self.elem, &self.semi_token, &self.len),
            back: (),
        }
        .locate(locator, code, offset)
    }
}

impl Locate for syn::TypeBareFn {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        Surround {
            front: (&self.lifetimes, &self.unsafety, &self.abi, &self.fn_token),
            surround: &self.paren_token,
            inner: (&self.inputs, &self.variadic),
            back: &self.output,
        }
        .locate(locator, code, offset)
    }
}

impl Locate for syn::TypeGroup {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        (&self.group_token, &self.elem).locate_as_group(locator, code, offset)
    }
}

impl Locate for syn::TypeImplTrait {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        (&self.impl_token, &self.bounds).locate_as_group(locator, code, offset)
    }
}

impl Locate for syn::TypeInfer {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        self.underscore_token.locate(locator, code, offset)
    }
}

impl Locate for syn::TypeMacro {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        self.mac.locate(locator, code, offset)
    }
}

impl Locate for syn::TypeNever {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        self.bang_token.locate(locator, code, offset)
    }
}

impl Locate for syn::TypeParen {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        Surround {
            front: (),
            surround: &self.paren_token,
            inner: &self.elem,
            back: (),
        }
        .locate(locator, code, offset)
    }
}

impl Locate for syn::TypePath {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        if let Some(qself) = &self.qself {
            Qualified {
                front: (),
                qself,
                path: &self.path,
                back: (),
            }
            .locate(locator, code, offset)
        } else {
            self.path.locate(locator, code, offset)
        }
    }
}

impl Locate for syn::TypePtr {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        (
            &self.star_token,
            &self.const_token,
            &self.mutability,
            &self.elem,
        )
            .locate_as_group(locator, code, offset)
    }
}

impl Locate for syn::TypeReference {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        (
            &self.and_token,
            &self.lifetime,
            &self.mutability,
            &self.elem,
        )
            .locate_as_group(locator, code, offset)
    }
}

impl Locate for syn::TypeSlice {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        Surround {
            front: (),
            surround: &self.bracket_token,
            inner: &self.elem,
            back: (),
        }
        .locate(locator, code, offset)
    }
}

impl Locate for syn::TypeTraitObject {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        (&self.dyn_token, &self.bounds).locate_as_group(locator, code, offset)
    }
}

impl Locate for syn::TypeTuple {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        Surround {
            front: (),
            surround: &self.paren_token,
            inner: &self.elems,
            back: (),
        }
        .locate(locator, code, offset)
    }
}

impl Locate for syn::TypeParam {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        (
            &self.attrs,
            &self.ident,
            &self.colon_token,
            &self.bounds,
            &self.eq_token,
            &self.default,
        )
            .locate_as_group(locator, code, offset)
    }
}

impl Locate for syn::TypeParamBound {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        match self {
            Self::Trait(v) => v.locate(locator, code, offset),
            Self::Lifetime(v) => v.locate(locator, code, offset),
            Self::PreciseCapture(v) => v.locate(locator, code, offset),
            Self::Verbatim(_) => Location {
                start: offset,
                end: offset,
            },
            _ => Location {
                start: offset,
                end: offset,
            },
        }
    }
}

impl Locate for syn::UnOp {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        match self {
            Self::Deref(v) => v.locate(locator, code, offset),
            Self::Not(v) => v.locate(locator, code, offset),
            Self::Neg(v) => v.locate(locator, code, offset),
            _ => Location {
                start: offset,
                end: offset,
            },
        }
    }
}

impl Locate for syn::UseGlob {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        self.star_token.locate(locator, code, offset)
    }
}

impl Locate for syn::UseGroup {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        Surround {
            front: (),
            surround: &self.brace_token,
            inner: &self.items,
            back: (),
        }
        .locate(locator, code, offset)
    }
}

impl Locate for syn::UseName {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        self.ident.locate(locator, code, offset)
    }
}

impl Locate for syn::UsePath {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        (&self.ident, &self.colon2_token, &self.tree).locate_as_group(locator, code, offset)
    }
}

impl Locate for syn::UseRename {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        (&self.ident, &self.as_token, &self.rename).locate_as_group(locator, code, offset)
    }
}

impl Locate for syn::UseTree {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        match self {
            Self::Path(v) => v.locate(locator, code, offset),
            Self::Name(v) => v.locate(locator, code, offset),
            Self::Rename(v) => v.locate(locator, code, offset),
            Self::Glob(v) => v.locate(locator, code, offset),
            Self::Group(v) => v.locate(locator, code, offset),
        }
    }
}

impl Locate for syn::Variadic {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        if let Some((pat, colon_token)) = &self.pat {
            (&self.attrs, pat, colon_token, &self.dots, &self.comma)
                .locate_as_group(locator, code, offset)
        } else {
            (&self.attrs, &self.dots, &self.comma).locate_as_group(locator, code, offset)
        }
    }
}

impl Locate for syn::Variant {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        if let Some((eq_token, discriminant)) = &self.discriminant {
            (
                &self.attrs,
                &self.ident,
                &self.fields,
                eq_token,
                discriminant,
            )
                .locate_as_group(locator, code, offset)
        } else {
            (&self.attrs, &self.ident, &self.fields).locate_as_group(locator, code, offset)
        }
    }
}

impl Locate for syn::Visibility {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        match self {
            Self::Public(v) => v.locate(locator, code, offset),
            Self::Restricted(v) => v.locate(locator, code, offset),
            Self::Inherited => Location {
                start: offset,
                end: offset,
            },
        }
    }
}

impl Locate for syn::VisRestricted {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        Surround {
            front: &self.pub_token,
            surround: &self.paren_token,
            inner: (&self.in_token, &self.path),
            back: (),
        }
        .locate(locator, code, offset)
    }
}

impl Locate for syn::WhereClause {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        (&self.where_token, &self.predicates).locate_as_group(locator, code, offset)
    }
}

impl Locate for syn::WherePredicate {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        match self {
            Self::Lifetime(v) => v.locate(locator, code, offset),
            Self::Type(v) => v.locate(locator, code, offset),
            _ => Location {
                start: offset,
                end: offset,
            },
        }
    }
}

/// A [`syn::WhereClause`] inside [`syn::Generics`] can appear outside the generic parameter list.
/// For example, in `impl<T> Trait for S<T> where T: Clone`, the where clause follows the self
/// type `S<T>`. Because of this, the location of `syn::Generics` has to be set manually.
fn locate_generics(locator: &mut Locator, generics: &syn::Generics) {
    let start = locator.get_location(&generics.lt_token).unwrap().start;

    let end = if generics.where_clause.is_some() {
        locator.get_location(&generics.where_clause).unwrap().end
    } else {
        let end = locator.get_location(&generics.gt_token).unwrap().end;

        // An empty `where_clause` would otherwise keep an unrelated fallback location, so place it
        // at the end of the generic parameter list.
        let loc = Location { start: end, end };
        generics.where_clause.relocate(locator, loc);

        end
    };

    // Set the location of `generics`.
    locator.set_location(generics, Location { start, end });
}

// === Composite types ===

impl<T: Locate> Locate for Option<T> {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        if let Some(inner) = self {
            inner.locate(locator, code, offset)
        } else {
            Location {
                start: offset,
                end: offset,
            }
        }
    }
}

impl<T: Locate> Locate for Box<T> {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        let t = &**self;
        t.locate(locator, code, offset)
    }
}

impl<T: Locate> Locate for Vec<T> {
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        let mut start = usize::MAX;
        let mut end = offset;

        for item in self {
            let loc = item.locate(locator, code, end);
            start = start.min(loc.start);
            end = loc.end;
        }

        Location {
            start: if start != usize::MAX { start } else { offset },
            end,
        }
    }
}

impl<T, S> Locate for syn::punctuated::Punctuated<T, S>
where
    T: Locate,
    S: Locate,
{
    fn find_loc(&self, locator: &mut Locator, code: &str, offset: usize) -> Location {
        let mut start = usize::MAX;
        let mut end = offset;

        for item in self {
            let loc = item.locate(locator, code, end);
            start = start.min(loc.start);
            end = loc.end;
        }

        Location {
            start: if start != usize::MAX { start } else { offset },
            end,
        }
    }
}

// === Helper functions ===

/// Low-level helpers for locating literal token text.
pub mod helper {
    use super::*;

    /// Finds the next occurrence of a character token at or after `offset`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use syn_locator::helper;
    ///
    /// let code = "fn foo() {}";
    /// let loc = helper::char_location(code, 0, '(');
    ///
    /// assert_eq!(loc.start, 6);
    /// assert_eq!(loc.end, 7);
    /// ```
    pub fn char_location(code: &str, offset: usize, content: char) -> Location {
        let cur_code = &code[offset..];
        let start = offset
            + cur_code
                .find(content)
                .unwrap_or_else(|| panic!("expected `{content}` from `{cur_code}`"));

        Location {
            start,
            end: start + content.len_utf8(),
        }
    }

    /// Finds the next occurrence of a string token at or after `offset`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use syn_locator::helper;
    ///
    /// let code = "fn foo() {}";
    /// let loc = helper::str_location(code, 0, "foo");
    ///
    /// assert_eq!(loc.start, 3);
    /// assert_eq!(loc.end, 6);
    /// ```
    pub fn str_location(code: &str, offset: usize, content: &str) -> Location {
        let cur_code = &code[offset..];

        let start = offset
            + cur_code
                .find(content)
                .unwrap_or_else(|| panic!("expected `{content}` from `{cur_code}`"));

        Location {
            start,
            end: start + content.len(),
        }
    }
}
