use super::Locate;
use std::any::{Any, TypeId};

pub trait Find<Output: Any> {
    fn find(&self, code: &str) -> Option<&Output>;
}

impl<O, T> Find<O> for T
where
    O: Any,
    T: FindPtr,
{
    fn find(&self, code: &str) -> Option<&O> {
        self.find_ptr(TypeId::of::<O>(), code)
            .map(|ptr| unsafe { (ptr as *const O).as_ref().unwrap() })
    }
}

pub trait FindPtr {
    fn find_ptr(&self, target: TypeId, code: &str) -> Option<*const ()>;
}

impl<T: FindPtr> FindPtr for Option<T> {
    fn find_ptr(&self, target: TypeId, code: &str) -> Option<*const ()> {
        self.as_ref()?.find_ptr(target, code)
    }
}

impl<T: FindPtr> FindPtr for Box<T> {
    fn find_ptr(&self, target: TypeId, code: &str) -> Option<*const ()> {
        self.as_ref().find_ptr(target, code)
    }
}

impl<T: FindPtr> FindPtr for Vec<T> {
    fn find_ptr(&self, target: TypeId, code: &str) -> Option<*const ()> {
        self.iter().find_map(|elem| elem.find_ptr(target, code))
    }
}

impl<T: FindPtr, P> FindPtr for syn::punctuated::Punctuated<T, P> {
    fn find_ptr(&self, target: TypeId, code: &str) -> Option<*const ()> {
        self.iter().find_map(|elem| elem.find_ptr(target, code))
    }
}

impl<T0, T1> FindPtr for (T0, T1)
where
    T0: FindPtr,
    T1: FindPtr,
{
    fn find_ptr(&self, target: TypeId, code: &str) -> Option<*const ()> {
        self.0
            .find_ptr(target, code)
            .or_else(|| self.1.find_ptr(target, code))
    }
}

impl<T0, T1, T2> FindPtr for (T0, T1, T2)
where
    T0: FindPtr,
    T1: FindPtr,
    T2: FindPtr,
{
    fn find_ptr(&self, target: TypeId, code: &str) -> Option<*const ()> {
        self.0
            .find_ptr(target, code)
            .or_else(|| self.1.find_ptr(target, code))
            .or_else(|| self.2.find_ptr(target, code))
    }
}

macro_rules! compare_then_return_if_target {
    ($self:expr, $target:expr, $code:expr) => {
        if $self.type_id() == $target && $self.code() == $code {
            return Some($self as *const _ as *const ());
        }
    };
}

macro_rules! impl_find_ptr_for_token {
    ($ty:ty) => {
        impl FindPtr for $ty {
            fn find_ptr(&self, target: TypeId, code: &str) -> Option<*const ()> {
                compare_then_return_if_target!(self, target, code);
                None
            }
        }
    };
}

impl_find_ptr_for_token!(syn::Token![abstract]);
impl_find_ptr_for_token!(syn::Token![as]);
impl_find_ptr_for_token!(syn::Token![async]);
impl_find_ptr_for_token!(syn::Token![auto]);
impl_find_ptr_for_token!(syn::Token![await]);
impl_find_ptr_for_token!(syn::Token![become]);
impl_find_ptr_for_token!(syn::Token![box]);
impl_find_ptr_for_token!(syn::Token![break]);
impl_find_ptr_for_token!(syn::Token![const]);
impl_find_ptr_for_token!(syn::Token![continue]);
impl_find_ptr_for_token!(syn::Token![crate]);
impl_find_ptr_for_token!(syn::Token![default]);
impl_find_ptr_for_token!(syn::Token![do]);
impl_find_ptr_for_token!(syn::Token![dyn]);
impl_find_ptr_for_token!(syn::Token![else]);
impl_find_ptr_for_token!(syn::Token![enum]);
impl_find_ptr_for_token!(syn::Token![extern]);
impl_find_ptr_for_token!(syn::Token![final]);
impl_find_ptr_for_token!(syn::Token![fn]);
impl_find_ptr_for_token!(syn::Token![for]);
impl_find_ptr_for_token!(syn::Token![if]);
impl_find_ptr_for_token!(syn::Token![impl]);
impl_find_ptr_for_token!(syn::Token![in]);
impl_find_ptr_for_token!(syn::Token![let]);
impl_find_ptr_for_token!(syn::Token![loop]);
impl_find_ptr_for_token!(syn::Token![macro]);
impl_find_ptr_for_token!(syn::Token![match]);
impl_find_ptr_for_token!(syn::Token![mod]);
impl_find_ptr_for_token!(syn::Token![move]);
impl_find_ptr_for_token!(syn::Token![mut]);
impl_find_ptr_for_token!(syn::Token![override]);
impl_find_ptr_for_token!(syn::Token![priv]);
impl_find_ptr_for_token!(syn::Token![pub]);
impl_find_ptr_for_token!(syn::Token![raw]);
impl_find_ptr_for_token!(syn::Token![ref]);
impl_find_ptr_for_token!(syn::Token![return]);
impl_find_ptr_for_token!(syn::Token![Self]);
impl_find_ptr_for_token!(syn::Token![self]);
impl_find_ptr_for_token!(syn::Token![static]);
impl_find_ptr_for_token!(syn::Token![struct]);
impl_find_ptr_for_token!(syn::Token![super]);
impl_find_ptr_for_token!(syn::Token![trait]);
impl_find_ptr_for_token!(syn::Token![try]);
impl_find_ptr_for_token!(syn::Token![type]);
impl_find_ptr_for_token!(syn::Token![typeof]);
impl_find_ptr_for_token!(syn::Token![union]);
impl_find_ptr_for_token!(syn::Token![unsafe]);
impl_find_ptr_for_token!(syn::Token![unsized]);
impl_find_ptr_for_token!(syn::Token![use]);
impl_find_ptr_for_token!(syn::Token![virtual]);
impl_find_ptr_for_token!(syn::Token![where]);
impl_find_ptr_for_token!(syn::Token![while]);
impl_find_ptr_for_token!(syn::Token![yield]);
impl_find_ptr_for_token!(syn::Token![&]);
impl_find_ptr_for_token!(syn::Token![&&]);
impl_find_ptr_for_token!(syn::Token![&=]);
impl_find_ptr_for_token!(syn::Token![@]);
impl_find_ptr_for_token!(syn::Token![^]);
impl_find_ptr_for_token!(syn::Token![^=]);
impl_find_ptr_for_token!(syn::Token![:]);
impl_find_ptr_for_token!(syn::Token![,]);
impl_find_ptr_for_token!(syn::Token![$]);
impl_find_ptr_for_token!(syn::Token![.]);
impl_find_ptr_for_token!(syn::Token![..]);
impl_find_ptr_for_token!(syn::Token![...]);
impl_find_ptr_for_token!(syn::Token![..=]);
impl_find_ptr_for_token!(syn::Token![=]);
impl_find_ptr_for_token!(syn::Token![==]);
impl_find_ptr_for_token!(syn::Token![=>]);
impl_find_ptr_for_token!(syn::Token![>=]);
impl_find_ptr_for_token!(syn::Token![>]);
impl_find_ptr_for_token!(syn::Token![<-]);
impl_find_ptr_for_token!(syn::Token![<=]);
impl_find_ptr_for_token!(syn::Token![<]);
impl_find_ptr_for_token!(syn::Token![-]);
impl_find_ptr_for_token!(syn::Token![-=]);
impl_find_ptr_for_token!(syn::Token![!=]);
impl_find_ptr_for_token!(syn::Token![!]);
impl_find_ptr_for_token!(syn::Token![|]);
impl_find_ptr_for_token!(syn::Token![|=]);
impl_find_ptr_for_token!(syn::Token![||]);
impl_find_ptr_for_token!(syn::Token![::]);
impl_find_ptr_for_token!(syn::Token![%]);
impl_find_ptr_for_token!(syn::Token![%=]);
impl_find_ptr_for_token!(syn::Token![+]);
impl_find_ptr_for_token!(syn::Token![+=]);
impl_find_ptr_for_token!(syn::Token![#]);
impl_find_ptr_for_token!(syn::Token![?]);
impl_find_ptr_for_token!(syn::Token![->]);
impl_find_ptr_for_token!(syn::Token![;]);
impl_find_ptr_for_token!(syn::Token![<<]);
impl_find_ptr_for_token!(syn::Token![<<=]);
impl_find_ptr_for_token!(syn::Token![>>]);
impl_find_ptr_for_token!(syn::Token![>>=]);
impl_find_ptr_for_token!(syn::Token![/]);
impl_find_ptr_for_token!(syn::Token![/=]);
impl_find_ptr_for_token!(syn::Token![*]);
impl_find_ptr_for_token!(syn::Token![*=]);
impl_find_ptr_for_token!(syn::Token![~]);
impl_find_ptr_for_token!(syn::Token![_]);
impl_find_ptr_for_token!(syn::token::Group);
impl_find_ptr_for_token!(syn::token::Brace);
impl_find_ptr_for_token!(syn::token::Bracket);
impl_find_ptr_for_token!(syn::token::Paren);

macro_rules! impl_find_ptr_simple {
    ($ty:ty) => {
        impl FindPtr for $ty {
            fn find_ptr(&self, target: TypeId, code: &str) -> Option<*const ()> {
                compare_then_return_if_target!(self, target, code);
                None
            }
        }
    };
    ($ty:ty, $first:ident) => {
        impl FindPtr for $ty {
            fn find_ptr(&self, target: TypeId, code: &str) -> Option<*const ()> {
                compare_then_return_if_target!(self, target, code);
                self.$first.find_ptr(target, code)
            }
        }
    };
    ($ty:ty, $first:ident, $($rest:ident),+) => {
        impl FindPtr for $ty {
            fn find_ptr(&self, target: TypeId, code: &str) -> Option<*const ()> {
                compare_then_return_if_target!(self, target, code);
                self.$first.find_ptr(target, code)
                $(
                    .or_else(|| self.$rest.find_ptr(target, code))
                )*
            }
        }
    };
}

impl_find_ptr_simple!(syn::Abi, extern_token, name);
impl_find_ptr_simple!(
    syn::AngleBracketedGenericArguments,
    colon2_token,
    lt_token,
    args,
    gt_token
);
impl_find_ptr_simple!(syn::Arm, attrs, pat, guard, fat_arrow_token, body, comma);
impl_find_ptr_simple!(syn::AssocConst, ident, generics, eq_token, value);
impl_find_ptr_simple!(syn::AssocType, ident, generics, eq_token, ty);
impl_find_ptr_simple!(syn::Attribute, pound_token, style, bracket_token, meta);
impl FindPtr for syn::AttrStyle {
    fn find_ptr(&self, target: TypeId, code: &str) -> Option<*const ()> {
        compare_then_return_if_target!(self, target, code);
        match self {
            Self::Outer => None,
            Self::Inner(v) => v.find_ptr(target, code),
        }
    }
}
impl_find_ptr_simple!(syn::BareFnArg, attrs, name, ty);
impl_find_ptr_simple!(syn::BareVariadic, attrs, name, dots, comma);
impl FindPtr for syn::BinOp {
    fn find_ptr(&self, target: TypeId, code: &str) -> Option<*const ()> {
        compare_then_return_if_target!(self, target, code);
        match self {
            Self::Add(v) => v.find_ptr(target, code),
            Self::Sub(v) => v.find_ptr(target, code),
            Self::Mul(v) => v.find_ptr(target, code),
            Self::Div(v) => v.find_ptr(target, code),
            Self::Rem(v) => v.find_ptr(target, code),
            Self::And(v) => v.find_ptr(target, code),
            Self::Or(v) => v.find_ptr(target, code),
            Self::BitXor(v) => v.find_ptr(target, code),
            Self::BitAnd(v) => v.find_ptr(target, code),
            Self::BitOr(v) => v.find_ptr(target, code),
            Self::Shl(v) => v.find_ptr(target, code),
            Self::Shr(v) => v.find_ptr(target, code),
            Self::Eq(v) => v.find_ptr(target, code),
            Self::Lt(v) => v.find_ptr(target, code),
            Self::Le(v) => v.find_ptr(target, code),
            Self::Ne(v) => v.find_ptr(target, code),
            Self::Ge(v) => v.find_ptr(target, code),
            Self::Gt(v) => v.find_ptr(target, code),
            Self::AddAssign(v) => v.find_ptr(target, code),
            Self::SubAssign(v) => v.find_ptr(target, code),
            Self::MulAssign(v) => v.find_ptr(target, code),
            Self::DivAssign(v) => v.find_ptr(target, code),
            Self::RemAssign(v) => v.find_ptr(target, code),
            Self::BitXorAssign(v) => v.find_ptr(target, code),
            Self::BitAndAssign(v) => v.find_ptr(target, code),
            Self::BitOrAssign(v) => v.find_ptr(target, code),
            Self::ShlAssign(v) => v.find_ptr(target, code),
            Self::ShrAssign(v) => v.find_ptr(target, code),
            _ => None,
        }
    }
}
impl_find_ptr_simple!(syn::Block, brace_token, stmts);
impl_find_ptr_simple!(
    syn::BoundLifetimes,
    for_token,
    lt_token,
    lifetimes,
    gt_token
);
impl FindPtr for syn::CapturedParam {
    fn find_ptr(&self, target: TypeId, code: &str) -> Option<*const ()> {
        compare_then_return_if_target!(self, target, code);
        match self {
            Self::Lifetime(v) => v.find_ptr(target, code),
            Self::Ident(v) => v.find_ptr(target, code),
            _ => None,
        }
    }
}
impl_find_ptr_simple!(
    syn::ConstParam,
    attrs,
    const_token,
    ident,
    colon_token,
    ty,
    eq_token,
    default
);
impl_find_ptr_simple!(syn::Constraint, ident, generics, colon_token, bounds);
impl FindPtr for syn::Expr {
    fn find_ptr(&self, target: TypeId, code: &str) -> Option<*const ()> {
        compare_then_return_if_target!(self, target, code);
        match self {
            Self::Array(v) => v.find_ptr(target, code),
            Self::Assign(v) => v.find_ptr(target, code),
            Self::Async(v) => v.find_ptr(target, code),
            Self::Await(v) => v.find_ptr(target, code),
            Self::Binary(v) => v.find_ptr(target, code),
            Self::Block(v) => v.find_ptr(target, code),
            Self::Break(v) => v.find_ptr(target, code),
            Self::Call(v) => v.find_ptr(target, code),
            Self::Cast(v) => v.find_ptr(target, code),
            Self::Closure(v) => v.find_ptr(target, code),
            Self::Const(v) => v.find_ptr(target, code),
            Self::Continue(v) => v.find_ptr(target, code),
            Self::Field(v) => v.find_ptr(target, code),
            Self::ForLoop(v) => v.find_ptr(target, code),
            Self::Group(v) => v.find_ptr(target, code),
            Self::If(v) => v.find_ptr(target, code),
            Self::Index(v) => v.find_ptr(target, code),
            Self::Infer(v) => v.find_ptr(target, code),
            Self::Let(v) => v.find_ptr(target, code),
            Self::Lit(v) => v.find_ptr(target, code),
            Self::Loop(v) => v.find_ptr(target, code),
            Self::Macro(v) => v.find_ptr(target, code),
            Self::Match(v) => v.find_ptr(target, code),
            Self::MethodCall(v) => v.find_ptr(target, code),
            Self::Paren(v) => v.find_ptr(target, code),
            Self::Path(v) => v.find_ptr(target, code),
            Self::Range(v) => v.find_ptr(target, code),
            Self::RawAddr(v) => v.find_ptr(target, code),
            Self::Reference(v) => v.find_ptr(target, code),
            Self::Repeat(v) => v.find_ptr(target, code),
            Self::Return(v) => v.find_ptr(target, code),
            Self::Struct(v) => v.find_ptr(target, code),
            Self::Try(v) => v.find_ptr(target, code),
            Self::TryBlock(v) => v.find_ptr(target, code),
            Self::Tuple(v) => v.find_ptr(target, code),
            Self::Unary(v) => v.find_ptr(target, code),
            Self::Unsafe(v) => v.find_ptr(target, code),
            Self::Verbatim(_) => None,
            Self::While(v) => v.find_ptr(target, code),
            Self::Yield(v) => v.find_ptr(target, code),
            _ => None,
        }
    }
}
impl_find_ptr_simple!(syn::ExprArray, attrs, elems);
impl_find_ptr_simple!(syn::ExprAssign, attrs, left, eq_token, right);
impl_find_ptr_simple!(syn::ExprAsync, attrs, async_token, capture, block);
impl_find_ptr_simple!(syn::ExprAwait, attrs, base, dot_token, await_token);
impl_find_ptr_simple!(syn::ExprBinary, attrs, left, op, right);
impl_find_ptr_simple!(syn::ExprBlock, attrs, label, block);
impl_find_ptr_simple!(syn::ExprBreak, attrs, break_token, label, expr);
impl_find_ptr_simple!(syn::ExprCall, attrs, func, paren_token, args);
impl_find_ptr_simple!(syn::ExprCast, attrs, expr, as_token, ty);
impl_find_ptr_simple!(
    syn::ExprClosure,
    attrs,
    lifetimes,
    constness,
    movability,
    asyncness,
    capture,
    or1_token,
    inputs,
    or2_token,
    output,
    body
);
impl_find_ptr_simple!(syn::ExprConst, attrs, const_token, block);
impl_find_ptr_simple!(syn::ExprContinue, attrs, continue_token, label);
impl_find_ptr_simple!(syn::ExprField, attrs, base, dot_token, member);
impl_find_ptr_simple!(
    syn::ExprForLoop,
    attrs,
    label,
    for_token,
    pat,
    in_token,
    expr,
    body
);
impl_find_ptr_simple!(syn::ExprGroup, attrs, group_token, expr);
impl_find_ptr_simple!(syn::ExprIf, attrs, if_token, cond, then_branch, else_branch);
impl_find_ptr_simple!(syn::ExprIndex, attrs, expr, bracket_token, index);
impl_find_ptr_simple!(syn::ExprInfer, attrs, underscore_token);
impl_find_ptr_simple!(syn::ExprLet, attrs, let_token, pat, eq_token, expr);
impl_find_ptr_simple!(syn::ExprLit, attrs, lit);
impl_find_ptr_simple!(syn::ExprLoop, attrs, label, loop_token, body);
impl_find_ptr_simple!(syn::ExprMacro, attrs, mac);
impl_find_ptr_simple!(syn::ExprMatch, attrs, match_token, expr, brace_token, arms);
impl_find_ptr_simple!(
    syn::ExprMethodCall,
    attrs,
    receiver,
    dot_token,
    method,
    turbofish,
    paren_token,
    args
);
impl_find_ptr_simple!(syn::ExprParen, attrs, paren_token, expr);
impl_find_ptr_simple!(syn::ExprPath, attrs, qself, path);
impl_find_ptr_simple!(syn::ExprRange, attrs, start, limits, end);
impl_find_ptr_simple!(syn::ExprRawAddr, attrs, and_token, raw, mutability, expr);
impl_find_ptr_simple!(syn::ExprReference, attrs, and_token, mutability, expr);
impl_find_ptr_simple!(syn::ExprRepeat, attrs, bracket_token, expr, semi_token, len);
impl_find_ptr_simple!(syn::ExprReturn, attrs, return_token, expr);
impl_find_ptr_simple!(
    syn::ExprStruct,
    attrs,
    qself,
    path,
    brace_token,
    fields,
    dot2_token,
    rest
);
impl_find_ptr_simple!(syn::ExprTry, attrs, expr, question_token);
impl_find_ptr_simple!(syn::ExprTryBlock, attrs, try_token, block);
impl_find_ptr_simple!(syn::ExprTuple, attrs, paren_token, elems);
impl_find_ptr_simple!(syn::ExprUnary, attrs, op, expr);
impl_find_ptr_simple!(syn::ExprUnsafe, attrs, unsafe_token, block);
impl_find_ptr_simple!(syn::ExprWhile, attrs, label, while_token, cond, body);
impl_find_ptr_simple!(syn::ExprYield, attrs, yield_token, expr);
impl_find_ptr_simple!(syn::Field, attrs, vis, mutability, ident, colon_token, ty);
impl FindPtr for syn::FieldMutability {
    fn find_ptr(&self, target: TypeId, code: &str) -> Option<*const ()> {
        compare_then_return_if_target!(self, target, code);
        None
    }
}
impl_find_ptr_simple!(syn::FieldPat, attrs, member, colon_token, pat);
impl FindPtr for syn::Fields {
    fn find_ptr(&self, target: TypeId, code: &str) -> Option<*const ()> {
        compare_then_return_if_target!(self, target, code);
        match self {
            Self::Named(v) => v.find_ptr(target, code),
            Self::Unnamed(v) => v.find_ptr(target, code),
            Self::Unit => None,
        }
    }
}
impl_find_ptr_simple!(syn::FieldsNamed, brace_token, named);
impl_find_ptr_simple!(syn::FieldsUnnamed, paren_token, unnamed);
impl_find_ptr_simple!(syn::FieldValue, attrs, member, colon_token, expr);
impl_find_ptr_simple!(syn::File, /*shebang*/ attrs, items);
impl FindPtr for syn::FnArg {
    fn find_ptr(&self, target: TypeId, code: &str) -> Option<*const ()> {
        compare_then_return_if_target!(self, target, code);
        match self {
            Self::Receiver(v) => v.find_ptr(target, code),
            Self::Typed(v) => v.find_ptr(target, code),
        }
    }
}
impl FindPtr for syn::ForeignItem {
    fn find_ptr(&self, target: TypeId, code: &str) -> Option<*const ()> {
        compare_then_return_if_target!(self, target, code);
        match self {
            Self::Fn(v) => v.find_ptr(target, code),
            Self::Static(v) => v.find_ptr(target, code),
            Self::Type(v) => v.find_ptr(target, code),
            Self::Macro(v) => v.find_ptr(target, code),
            Self::Verbatim(_) => None,
            _ => None,
        }
    }
}
impl_find_ptr_simple!(syn::ForeignItemFn, attrs, vis, sig, semi_token);
impl_find_ptr_simple!(
    syn::ForeignItemStatic,
    attrs,
    vis,
    static_token,
    mutability,
    ident,
    colon_token,
    ty,
    semi_token
);
impl_find_ptr_simple!(
    syn::ForeignItemType,
    attrs,
    vis,
    type_token,
    ident,
    generics,
    semi_token
);
impl_find_ptr_simple!(syn::ForeignItemMacro, attrs, mac, semi_token);
impl FindPtr for syn::GenericArgument {
    fn find_ptr(&self, target: TypeId, code: &str) -> Option<*const ()> {
        compare_then_return_if_target!(self, target, code);
        match self {
            Self::Lifetime(v) => v.find_ptr(target, code),
            Self::Type(v) => v.find_ptr(target, code),
            Self::Const(v) => v.find_ptr(target, code),
            Self::AssocType(v) => v.find_ptr(target, code),
            Self::AssocConst(v) => v.find_ptr(target, code),
            Self::Constraint(v) => v.find_ptr(target, code),
            _ => None,
        }
    }
}
impl FindPtr for syn::GenericParam {
    fn find_ptr(&self, target: TypeId, code: &str) -> Option<*const ()> {
        compare_then_return_if_target!(self, target, code);
        match self {
            Self::Lifetime(v) => v.find_ptr(target, code),
            Self::Type(v) => v.find_ptr(target, code),
            Self::Const(v) => v.find_ptr(target, code),
        }
    }
}
impl_find_ptr_simple!(syn::Generics, lt_token, params, gt_token, where_clause);
impl_find_ptr_simple!(syn::Ident);
impl FindPtr for syn::ImplItem {
    fn find_ptr(&self, target: TypeId, code: &str) -> Option<*const ()> {
        compare_then_return_if_target!(self, target, code);
        match self {
            Self::Const(v) => v.find_ptr(target, code),
            Self::Fn(v) => v.find_ptr(target, code),
            Self::Type(v) => v.find_ptr(target, code),
            Self::Macro(v) => v.find_ptr(target, code),
            Self::Verbatim(_) => None,
            _ => None,
        }
    }
}
impl_find_ptr_simple!(
    syn::ImplItemConst,
    attrs,
    vis,
    defaultness,
    const_token,
    ident,
    generics,
    colon_token,
    ty,
    eq_token,
    expr,
    semi_token
);
impl_find_ptr_simple!(syn::ImplItemFn, attrs, vis, defaultness, sig, block);
impl_find_ptr_simple!(
    syn::ImplItemType,
    attrs,
    vis,
    defaultness,
    type_token,
    ident,
    generics,
    eq_token,
    ty,
    semi_token
);
impl_find_ptr_simple!(syn::ImplItemMacro, attrs, mac, semi_token);
impl FindPtr for syn::ImplRestriction {
    fn find_ptr(&self, target: TypeId, code: &str) -> Option<*const ()> {
        compare_then_return_if_target!(self, target, code);
        #[allow(clippy::match_single_binding)]
        match self {
            _ => None,
        }
    }
}
impl_find_ptr_simple!(syn::Index);
impl FindPtr for syn::Item {
    fn find_ptr(&self, target: TypeId, code: &str) -> Option<*const ()> {
        compare_then_return_if_target!(self, target, code);
        match self {
            Self::Const(v) => v.find_ptr(target, code),
            Self::Enum(v) => v.find_ptr(target, code),
            Self::ExternCrate(v) => v.find_ptr(target, code),
            Self::Fn(v) => v.find_ptr(target, code),
            Self::ForeignMod(v) => v.find_ptr(target, code),
            Self::Impl(v) => v.find_ptr(target, code),
            Self::Macro(v) => v.find_ptr(target, code),
            Self::Mod(v) => v.find_ptr(target, code),
            Self::Static(v) => v.find_ptr(target, code),
            Self::Struct(v) => v.find_ptr(target, code),
            Self::Trait(v) => v.find_ptr(target, code),
            Self::TraitAlias(v) => v.find_ptr(target, code),
            Self::Type(v) => v.find_ptr(target, code),
            Self::Union(v) => v.find_ptr(target, code),
            Self::Use(v) => v.find_ptr(target, code),
            Self::Verbatim(_) => None,
            _ => None,
        }
    }
}
impl_find_ptr_simple!(
    syn::ItemConst,
    attrs,
    vis,
    const_token,
    ident,
    generics,
    colon_token,
    ty,
    eq_token,
    expr,
    semi_token
);
impl_find_ptr_simple!(
    syn::ItemEnum,
    attrs,
    vis,
    enum_token,
    ident,
    generics,
    brace_token,
    variants
);
impl_find_ptr_simple!(
    syn::ItemExternCrate,
    attrs,
    vis,
    extern_token,
    crate_token,
    ident,
    rename,
    semi_token
);
impl_find_ptr_simple!(syn::ItemFn, attrs, vis, sig, block);
impl_find_ptr_simple!(
    syn::ItemForeignMod,
    attrs,
    unsafety,
    abi,
    brace_token,
    items
);
impl_find_ptr_simple!(
    syn::ItemImpl,
    attrs,
    defaultness,
    unsafety,
    impl_token,
    generics,
    trait_,
    self_ty,
    brace_token,
    items
);

// Parse order is not the same as the order they are declared.
// ref: https://github.com/dtolnay/syn/blob/5357c8fb6bd29fd7c829e0aede1dab4b45a6e00f/src/item.rs#L1240
impl FindPtr for syn::ItemMacro {
    fn find_ptr(&self, target: TypeId, code: &str) -> Option<*const ()> {
        compare_then_return_if_target!(self, target, code);
        self.attrs
            .find_ptr(target, code)
            .or_else(|| self.mac.path.find_ptr(target, code))
            .or_else(|| self.mac.bang_token.find_ptr(target, code))
            .or_else(|| self.ident.find_ptr(target, code))
            .or_else(|| self.semi_token.find_ptr(target, code))
    }
}
impl_find_ptr_simple!(
    syn::ItemMod,
    attrs,
    vis,
    unsafety,
    mod_token,
    ident,
    content,
    semi
);
impl_find_ptr_simple!(
    syn::ItemStatic,
    attrs,
    vis,
    static_token,
    mutability,
    ident,
    colon_token,
    ty,
    eq_token,
    expr,
    semi_token
);
impl_find_ptr_simple!(
    syn::ItemStruct,
    attrs,
    vis,
    struct_token,
    ident,
    generics,
    fields,
    semi_token
);
impl_find_ptr_simple!(
    syn::ItemTrait,
    attrs,
    vis,
    unsafety,
    auto_token,
    restriction,
    trait_token,
    ident,
    generics,
    colon_token,
    supertraits,
    brace_token,
    items
);
impl_find_ptr_simple!(
    syn::ItemTraitAlias,
    attrs,
    vis,
    trait_token,
    ident,
    generics,
    eq_token,
    bounds,
    semi_token
);
impl_find_ptr_simple!(
    syn::ItemType,
    attrs,
    vis,
    type_token,
    ident,
    generics,
    eq_token,
    ty,
    semi_token
);
impl_find_ptr_simple!(
    syn::ItemUnion,
    attrs,
    vis,
    union_token,
    ident,
    generics,
    fields
);
impl_find_ptr_simple!(
    syn::ItemUse,
    attrs,
    vis,
    use_token,
    leading_colon,
    tree,
    semi_token
);
impl_find_ptr_simple!(syn::Label, name, colon_token);
impl_find_ptr_simple!(syn::Lifetime, ident);
impl_find_ptr_simple!(syn::LifetimeParam, attrs, lifetime, colon_token, bounds);
impl FindPtr for syn::Lit {
    fn find_ptr(&self, target: TypeId, code: &str) -> Option<*const ()> {
        compare_then_return_if_target!(self, target, code);
        match self {
            Self::Str(v) => v.find_ptr(target, code),
            Self::ByteStr(v) => v.find_ptr(target, code),
            Self::CStr(v) => v.find_ptr(target, code),
            Self::Byte(v) => v.find_ptr(target, code),
            Self::Char(v) => v.find_ptr(target, code),
            Self::Int(v) => v.find_ptr(target, code),
            Self::Float(v) => v.find_ptr(target, code),
            Self::Bool(v) => v.find_ptr(target, code),
            Self::Verbatim(_) => None,
            _ => None,
        }
    }
}
impl_find_ptr_simple!(syn::LitStr);
impl_find_ptr_simple!(syn::LitByteStr);
impl_find_ptr_simple!(syn::LitCStr);
impl_find_ptr_simple!(syn::LitByte);
impl_find_ptr_simple!(syn::LitChar);
impl_find_ptr_simple!(syn::LitInt);
impl_find_ptr_simple!(syn::LitFloat);
impl_find_ptr_simple!(syn::LitBool);
impl_find_ptr_simple!(syn::Local, attrs, let_token, pat, init, semi_token);
impl_find_ptr_simple!(syn::LocalInit, eq_token, expr, diverge);
impl_find_ptr_simple!(syn::Macro, path, bang_token, delimiter /*tokens*/);
impl FindPtr for syn::MacroDelimiter {
    fn find_ptr(&self, target: TypeId, code: &str) -> Option<*const ()> {
        compare_then_return_if_target!(self, target, code);
        match self {
            Self::Paren(v) => v.find_ptr(target, code),
            Self::Brace(v) => v.find_ptr(target, code),
            Self::Bracket(v) => v.find_ptr(target, code),
        }
    }
}
impl FindPtr for syn::Member {
    fn find_ptr(&self, target: TypeId, code: &str) -> Option<*const ()> {
        compare_then_return_if_target!(self, target, code);
        match self {
            Self::Named(v) => v.find_ptr(target, code),
            Self::Unnamed(v) => v.find_ptr(target, code),
        }
    }
}
impl FindPtr for syn::Meta {
    fn find_ptr(&self, target: TypeId, code: &str) -> Option<*const ()> {
        compare_then_return_if_target!(self, target, code);
        match self {
            Self::Path(v) => v.find_ptr(target, code),
            Self::List(v) => v.find_ptr(target, code),
            Self::NameValue(v) => v.find_ptr(target, code),
        }
    }
}
impl_find_ptr_simple!(syn::MetaList, path, delimiter /*tokens*/);
impl_find_ptr_simple!(syn::MetaNameValue, path, eq_token, value);
impl_find_ptr_simple!(
    syn::ParenthesizedGenericArguments,
    paren_token,
    inputs,
    output
);
impl FindPtr for syn::Pat {
    fn find_ptr(&self, target: TypeId, code: &str) -> Option<*const ()> {
        compare_then_return_if_target!(self, target, code);
        match self {
            Self::Const(v) => v.find_ptr(target, code),
            Self::Ident(v) => v.find_ptr(target, code),
            Self::Lit(v) => v.find_ptr(target, code),
            Self::Macro(v) => v.find_ptr(target, code),
            Self::Or(v) => v.find_ptr(target, code),
            Self::Paren(v) => v.find_ptr(target, code),
            Self::Path(v) => v.find_ptr(target, code),
            Self::Range(v) => v.find_ptr(target, code),
            Self::Reference(v) => v.find_ptr(target, code),
            Self::Rest(v) => v.find_ptr(target, code),
            Self::Slice(v) => v.find_ptr(target, code),
            Self::Struct(v) => v.find_ptr(target, code),
            Self::Tuple(v) => v.find_ptr(target, code),
            Self::TupleStruct(v) => v.find_ptr(target, code),
            Self::Type(v) => v.find_ptr(target, code),
            Self::Verbatim(_) => None,
            Self::Wild(v) => v.find_ptr(target, code),
            _ => None,
        }
    }
}
impl_find_ptr_simple!(syn::PatIdent, attrs, by_ref, mutability, ident, subpat);
impl_find_ptr_simple!(syn::PatOr, attrs, leading_vert, cases);
impl_find_ptr_simple!(syn::PatParen, attrs, paren_token, pat);
impl_find_ptr_simple!(syn::PatReference, attrs, and_token, mutability, pat);
impl_find_ptr_simple!(syn::PatRest, attrs, dot2_token);
impl_find_ptr_simple!(syn::PatSlice, attrs, bracket_token, elems);
impl_find_ptr_simple!(
    syn::PatStruct,
    attrs,
    qself,
    path,
    brace_token,
    fields,
    rest
);
impl_find_ptr_simple!(syn::PatTuple, attrs, paren_token, elems);
impl_find_ptr_simple!(syn::PatTupleStruct, attrs, qself, path, paren_token, elems);
impl_find_ptr_simple!(syn::PatType, attrs, pat, colon_token, ty);
impl_find_ptr_simple!(syn::PatWild, attrs, underscore_token);
impl_find_ptr_simple!(syn::Path, leading_colon, segments);
impl FindPtr for syn::PathArguments {
    fn find_ptr(&self, target: TypeId, code: &str) -> Option<*const ()> {
        compare_then_return_if_target!(self, target, code);
        match self {
            Self::None => None,
            Self::AngleBracketed(v) => v.find_ptr(target, code),
            Self::Parenthesized(v) => v.find_ptr(target, code),
        }
    }
}
impl_find_ptr_simple!(syn::PathSegment, ident, arguments);
impl FindPtr for syn::PointerMutability {
    fn find_ptr(&self, target: TypeId, code: &str) -> Option<*const ()> {
        compare_then_return_if_target!(self, target, code);
        match self {
            Self::Const(v) => v.find_ptr(target, code),
            Self::Mut(v) => v.find_ptr(target, code),
        }
    }
}
impl_find_ptr_simple!(syn::PreciseCapture, use_token, lt_token, params, gt_token);
impl_find_ptr_simple!(syn::PredicateLifetime, lifetime, colon_token, bounds);
impl_find_ptr_simple!(
    syn::PredicateType,
    lifetimes,
    bounded_ty,
    colon_token,
    bounds
);

// We ignore 'as' token because it means the following `syn::Path` is mixed
// with this Qself.
impl_find_ptr_simple!(syn::QSelf, lt_token, ty, /*as_token*/ gt_token);
impl FindPtr for syn::RangeLimits {
    fn find_ptr(&self, target: TypeId, code: &str) -> Option<*const ()> {
        compare_then_return_if_target!(self, target, code);
        match self {
            Self::HalfOpen(v) => v.find_ptr(target, code),
            Self::Closed(v) => v.find_ptr(target, code),
        }
    }
}
impl FindPtr for syn::Receiver {
    fn find_ptr(&self, target: TypeId, code: &str) -> Option<*const ()> {
        // If there is no colon, `self.ty` must be ignored because it is not
        // constructed from source code.

        compare_then_return_if_target!(self, target, code);
        self.attrs
            .find_ptr(target, code)
            .or_else(|| self.reference.find_ptr(target, code))
            .or_else(|| self.mutability.find_ptr(target, code))
            .or_else(|| self.self_token.find_ptr(target, code))
            .or_else(|| self.colon_token.find_ptr(target, code))
            .or_else(|| {
                self.colon_token
                    .is_some()
                    .then(|| self.ty.find_ptr(target, code))
                    .flatten()
            })
    }
}
impl FindPtr for syn::ReturnType {
    fn find_ptr(&self, target: TypeId, code: &str) -> Option<*const ()> {
        compare_then_return_if_target!(self, target, code);
        match self {
            Self::Default => None,
            Self::Type(arrow, ty) => arrow
                .find_ptr(target, code)
                .or_else(|| ty.find_ptr(target, code)),
        }
    }
}
impl_find_ptr_simple!(
    syn::Signature,
    constness,
    asyncness,
    unsafety,
    abi,
    fn_token,
    ident,
    generics,
    paren_token,
    inputs,
    variadic,
    output
);
impl FindPtr for syn::StaticMutability {
    fn find_ptr(&self, target: TypeId, code: &str) -> Option<*const ()> {
        compare_then_return_if_target!(self, target, code);
        match self {
            Self::Mut(v) => v.find_ptr(target, code),
            Self::None => None,
            _ => None,
        }
    }
}
impl FindPtr for syn::Stmt {
    fn find_ptr(&self, target: TypeId, code: &str) -> Option<*const ()> {
        compare_then_return_if_target!(self, target, code);
        match self {
            Self::Local(v) => v.find_ptr(target, code),
            Self::Item(v) => v.find_ptr(target, code),
            Self::Expr(expr, semi) => expr
                .find_ptr(target, code)
                .or_else(|| semi.find_ptr(target, code)),
            Self::Macro(v) => v.find_ptr(target, code),
        }
    }
}
impl_find_ptr_simple!(syn::StmtMacro, attrs, mac, semi_token);
impl_find_ptr_simple!(syn::TraitBound, paren_token, modifier, lifetimes, path);
impl FindPtr for syn::TraitBoundModifier {
    fn find_ptr(&self, target: TypeId, code: &str) -> Option<*const ()> {
        compare_then_return_if_target!(self, target, code);
        match self {
            Self::None => None,
            Self::Maybe(v) => v.find_ptr(target, code),
        }
    }
}
impl FindPtr for syn::TraitItem {
    fn find_ptr(&self, target: TypeId, code: &str) -> Option<*const ()> {
        compare_then_return_if_target!(self, target, code);
        match self {
            Self::Const(v) => v.find_ptr(target, code),
            Self::Fn(v) => v.find_ptr(target, code),
            Self::Type(v) => v.find_ptr(target, code),
            Self::Macro(v) => v.find_ptr(target, code),
            Self::Verbatim(_) => None,
            _ => None,
        }
    }
}
impl_find_ptr_simple!(
    syn::TraitItemConst,
    attrs,
    const_token,
    ident,
    generics,
    colon_token,
    ty,
    default,
    semi_token
);
impl_find_ptr_simple!(syn::TraitItemFn, attrs, sig, default, semi_token);
impl_find_ptr_simple!(
    syn::TraitItemType,
    attrs,
    type_token,
    ident,
    generics,
    colon_token,
    bounds,
    default,
    semi_token
);
impl_find_ptr_simple!(syn::TraitItemMacro, attrs, mac, semi_token);
impl FindPtr for syn::Type {
    fn find_ptr(&self, target: TypeId, code: &str) -> Option<*const ()> {
        compare_then_return_if_target!(self, target, code);
        match self {
            Self::Array(v) => v.find_ptr(target, code),
            Self::BareFn(v) => v.find_ptr(target, code),
            Self::Group(v) => v.find_ptr(target, code),
            Self::ImplTrait(v) => v.find_ptr(target, code),
            Self::Infer(v) => v.find_ptr(target, code),
            Self::Macro(v) => v.find_ptr(target, code),
            Self::Never(v) => v.find_ptr(target, code),
            Self::Paren(v) => v.find_ptr(target, code),
            Self::Path(v) => v.find_ptr(target, code),
            Self::Ptr(v) => v.find_ptr(target, code),
            Self::Reference(v) => v.find_ptr(target, code),
            Self::Slice(v) => v.find_ptr(target, code),
            Self::TraitObject(v) => v.find_ptr(target, code),
            Self::Tuple(v) => v.find_ptr(target, code),
            Self::Verbatim(_) => None,
            _ => None,
        }
    }
}
impl_find_ptr_simple!(syn::TypeArray, bracket_token, elem, semi_token, len);
impl_find_ptr_simple!(
    syn::TypeBareFn,
    lifetimes,
    unsafety,
    abi,
    fn_token,
    paren_token,
    inputs,
    variadic,
    output
);
impl_find_ptr_simple!(syn::TypeGroup, group_token, elem);
impl_find_ptr_simple!(syn::TypeImplTrait, impl_token, bounds);
impl_find_ptr_simple!(syn::TypeInfer, underscore_token);
impl_find_ptr_simple!(syn::TypeMacro, mac);
impl_find_ptr_simple!(syn::TypeNever, bang_token);
impl_find_ptr_simple!(syn::TypeParen, paren_token, elem);
impl_find_ptr_simple!(syn::TypePath, qself, path);
impl_find_ptr_simple!(syn::TypePtr, star_token, const_token, mutability, elem);
impl_find_ptr_simple!(syn::TypeReference, and_token, lifetime, mutability, elem);
impl_find_ptr_simple!(syn::TypeSlice, bracket_token, elem);
impl_find_ptr_simple!(syn::TypeTraitObject, dyn_token, bounds);
impl_find_ptr_simple!(syn::TypeTuple, paren_token, elems);
impl_find_ptr_simple!(
    syn::TypeParam,
    attrs,
    ident,
    colon_token,
    bounds,
    eq_token,
    default
);
impl FindPtr for syn::TypeParamBound {
    fn find_ptr(&self, target: TypeId, code: &str) -> Option<*const ()> {
        compare_then_return_if_target!(self, target, code);
        match self {
            Self::Trait(v) => v.find_ptr(target, code),
            Self::Lifetime(v) => v.find_ptr(target, code),
            Self::PreciseCapture(v) => v.find_ptr(target, code),
            Self::Verbatim(_) => None,
            _ => None,
        }
    }
}
impl FindPtr for syn::UnOp {
    fn find_ptr(&self, target: TypeId, code: &str) -> Option<*const ()> {
        compare_then_return_if_target!(self, target, code);
        match self {
            Self::Deref(v) => v.find_ptr(target, code),
            Self::Not(v) => v.find_ptr(target, code),
            Self::Neg(v) => v.find_ptr(target, code),
            _ => None,
        }
    }
}
impl_find_ptr_simple!(syn::UseGlob, star_token);
impl_find_ptr_simple!(syn::UseGroup, brace_token, items);
impl_find_ptr_simple!(syn::UseName, ident);
impl_find_ptr_simple!(syn::UsePath, ident, colon2_token, tree);
impl_find_ptr_simple!(syn::UseRename, ident, as_token, rename);
impl FindPtr for syn::UseTree {
    fn find_ptr(&self, target: TypeId, code: &str) -> Option<*const ()> {
        compare_then_return_if_target!(self, target, code);
        match self {
            Self::Path(v) => v.find_ptr(target, code),
            Self::Name(v) => v.find_ptr(target, code),
            Self::Rename(v) => v.find_ptr(target, code),
            Self::Glob(v) => v.find_ptr(target, code),
            Self::Group(v) => v.find_ptr(target, code),
        }
    }
}
impl_find_ptr_simple!(syn::Variadic, attrs, pat, dots, comma);
impl_find_ptr_simple!(syn::Variant, attrs, ident, fields, discriminant);
impl FindPtr for syn::Visibility {
    fn find_ptr(&self, target: TypeId, code: &str) -> Option<*const ()> {
        compare_then_return_if_target!(self, target, code);
        match self {
            Self::Public(v) => v.find_ptr(target, code),
            Self::Restricted(v) => v.find_ptr(target, code),
            Self::Inherited => None,
        }
    }
}
impl_find_ptr_simple!(syn::VisRestricted, pub_token, paren_token, in_token, path);
impl_find_ptr_simple!(syn::WhereClause, where_token, predicates);
impl FindPtr for syn::WherePredicate {
    fn find_ptr(&self, target: TypeId, code: &str) -> Option<*const ()> {
        compare_then_return_if_target!(self, target, code);
        match self {
            Self::Lifetime(v) => v.find_ptr(target, code),
            Self::Type(v) => v.find_ptr(target, code),
            _ => None,
        }
    }
}
