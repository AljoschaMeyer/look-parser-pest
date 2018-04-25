use ast::*;

// An AST walker, similiar to https://help.eclipse.org/mars/index.jsp?topic=%2Forg.eclipse.jdt.doc.isv%2Freference%2Fapi%2Forg%2Feclipse%2Fjdt%2Fcore%2Fdom%2FJavadoc.html
//
// When reaching a node, it calls first calls the nodetype_pre_fn function. If it returns true, it
// recursively visits the child nodes. Then, it calls the nodetype_post_fn function. If a pre
// function returns false, the visitor directly proceeds with the corresponding post function.
//
// Leaf nodes only have one corresponding function.
//
// Unset functions behave as if they returned true (so a walker without any set functions traverses
// the whole ast, but does nothing).
pub struct AstWalkerMut {
    pub file_pre_fn: Option<Box<FnMut(&mut File) -> bool>>,
    pub file_post_fn: Option<Box<FnMut(&mut File)>>,

    pub attribute_pre_fn: Option<Box<FnMut(&mut Attribute) -> bool>>,
    pub attribute_post_fn: Option<Box<FnMut(&mut Attribute)>>,

    pub item_pre_fn: Option<Box<FnMut(&mut Item) -> bool>>,
    pub item_post_fn: Option<Box<FnMut(&mut Item)>>,

    pub use_prefix_fn: Option<Box<FnMut(&mut UsePrefix)>>,

    pub use_tree_pre_fn: Option<Box<FnMut(&mut UseTree) -> bool>>,
    pub use_tree_post_fn: Option<Box<FnMut(&mut UseTree)>>,

    pub simple_identifier_fn: Option<Box<FnMut(&mut SimpleIdentifier)>>,

    pub type_def_pre_fn: Option<Box<FnMut(&mut TypeDef) -> bool>>,
    pub type_def_post_fn: Option<Box<FnMut(&mut TypeDef)>>,

    pub pattern_pre_fn: Option<Box<FnMut(&mut Pattern) -> bool>>,
    pub pattern_post_fn: Option<Box<FnMut(&mut Pattern)>>,

    pub expression_pre_fn: Option<Box<FnMut(&mut Expression) -> bool>>,
    pub expression_post_fn: Option<Box<FnMut(&mut Expression)>>,

    pub ffi_language_fn: Option<Box<FnMut(&mut FfiLanguage)>>,

    pub ffi_item_pre_fn: Option<Box<FnMut(&mut FfiItem) -> bool>>,
    pub ffi_item_post_fn: Option<Box<FnMut(&mut FfiItem)>>,

    pub type_pre_fn: Option<Box<FnMut(&mut Type) -> bool>>,
    pub type_post_fn: Option<Box<FnMut(&mut Type)>>,

    pub summand_pre_fn: Option<Box<FnMut(&mut Summand) -> bool>>,
    pub summand_post_fn: Option<Box<FnMut(&mut Summand)>>,

    pub identifier_pre_fn: Option<Box<FnMut(&mut Identifier) -> bool>>,
    pub identifier_post_fn: Option<Box<FnMut(&mut Identifier)>>,

    pub literal_fn: Option<Box<FnMut(&mut Literal)>>,

    pub macro_invocation_pre_fn: Option<Box<FnMut(&mut MacroInvocation) -> bool>>,
    pub macro_invocation_post_fn: Option<Box<FnMut(&mut MacroInvocation)>>,

    pub repetition_pre_fn: Option<Box<FnMut(&mut Repetition) -> bool>>,
    pub repetition_post_fn: Option<Box<FnMut(&mut Repetition)>>,

    pub meta_item_pre_fn: Option<Box<FnMut(&mut MetaItem) -> bool>>,
    pub meta_item_post_fn: Option<Box<FnMut(&mut MetaItem)>>,
}

impl AstWalkerMut {
    pub fn new() -> AstWalkerMut {
        AstWalkerMut {
            file_pre_fn: None,
            file_post_fn: None,
            attribute_pre_fn: None,
            attribute_post_fn: None,
            item_pre_fn: None,
            item_post_fn: None,
            use_prefix_fn: None,
            use_tree_pre_fn: None,
            use_tree_post_fn: None,
            simple_identifier_fn: None,
            type_def_pre_fn: None,
            type_def_post_fn: None,
            pattern_pre_fn: None,
            pattern_post_fn: None,
            expression_pre_fn: None,
            expression_post_fn: None,
            ffi_language_fn: None,
            ffi_item_pre_fn: None,
            ffi_item_post_fn: None,
            type_pre_fn: None,
            type_post_fn: None,
            summand_pre_fn: None,
            summand_post_fn: None,
            identifier_pre_fn: None,
            identifier_post_fn: None,
            literal_fn: None,
            macro_invocation_pre_fn: None,
            macro_invocation_post_fn: None,
            repetition_pre_fn: None,
            repetition_post_fn: None,
            meta_item_pre_fn: None,
            meta_item_post_fn: None,
        }
    }

    pub fn walk_file(&mut self, file: &mut File) {
        if self.file_pre_fn.as_mut().map_or(true, |fun| fun(file)) {
            for &mut (ref mut attrs, ref mut item) in file.0.iter_mut() {
                for attr in attrs {
                    self.walk_attribute(attr);
                }
                self.walk_item(item);
            }
        }

        self.file_post_fn.as_mut().map(|fun| fun(file));
    }

    pub fn walk_attribute(&mut self, attr: &mut Attribute) {
        if self.attribute_pre_fn
               .as_mut()
               .map_or(true, |fun| fun(attr)) {
            self.walk_meta_item(&mut attr.0);
        }

        self.attribute_post_fn.as_mut().map(|fun| fun(attr));
    }

    pub fn walk_meta_item(&mut self, meta: &mut MetaItem) {
        if self.meta_item_pre_fn
               .as_mut()
               .map_or(true, |fun| fun(meta)) {
            match meta {
                &mut MetaItem::Nullary(ref mut sid, _) => self.walk_simple_identifier(sid),
                &mut MetaItem::Pair(ref mut sid, ref mut lit, _) => {
                    self.walk_simple_identifier(sid);
                    self.walk_literal(lit);
                }
                &mut MetaItem::LitArg(ref mut sid, ref mut lit, _) => {
                    self.walk_simple_identifier(sid);
                    self.walk_literal(lit);
                }
                &mut MetaItem::Args(ref mut sid, ref mut inner, _) => {
                    self.walk_simple_identifier(sid);
                    for inner_meta in inner {
                        self.walk_meta_item(inner_meta);
                    }
                }
            }
        }

        self.meta_item_post_fn.as_mut().map(|fun| fun(meta));
    }

    pub fn walk_simple_identifier(&mut self, sid: &mut SimpleIdentifier) {
        self.simple_identifier_fn.as_mut().map(|fun| fun(sid));
    }

    pub fn walk_literal(&mut self, lit: &mut Literal) {
        self.literal_fn.as_mut().map(|fun| fun(lit));
    }

    pub fn walk_item(&mut self, item: &mut Item) {
        if self.item_pre_fn.as_mut().map_or(true, |fun| fun(item)) {
            match item {
                &mut Item::Use(_, ref mut prefix, ref mut tree, _) => {
                    self.walk_use_prefix(prefix);
                    self.walk_use_tree(tree);
                }
                &mut Item::Type(_, ref mut sid, ref mut type_def, _) => {
                    self.walk_simple_identifier(sid);
                    self.walk_type_def(type_def);
                }
                &mut Item::Val(_, ref mut pattern, ref mut expression, _) => {
                    self.walk_pattern(pattern);
                    self.walk_expression(expression);
                }
                &mut Item::FfiBlock(ref mut ffi_language, ref mut ffi_items, _) => {
                    self.walk_ffi_language(ffi_language);
                    for &mut (ref mut attrs, ref mut ffi_item) in ffi_items {
                        for attr in attrs {
                            self.walk_attribute(attr);
                        }
                        self.walk_ffi_item(ffi_item);
                    }
                }
            }
        }

        self.item_post_fn.as_mut().map(|fun| fun(item));
    }

    pub fn walk_use_prefix(&mut self, prefix: &mut UsePrefix) {
        self.use_prefix_fn.as_mut().map(|fun| fun(prefix));
    }

    pub fn walk_use_tree(&mut self, tree: &mut UseTree) {
        if self.use_tree_pre_fn
               .as_mut()
               .map_or(true, |fun| fun(tree)) {
            match tree {
                &mut UseTree::IdLeaf(ref mut sid, _) => self.walk_simple_identifier(sid),
                &mut UseTree::SelfLeaf(_) => {}
                &mut UseTree::IdRenamedLeaf(ref mut sid, ref mut new_name, _) => {
                    self.walk_simple_identifier(sid);
                    self.walk_simple_identifier(new_name);
                }
                &mut UseTree::SelfRenamedLeaf(ref mut sid, _) => self.walk_simple_identifier(sid),
                &mut UseTree::IdBranch(ref mut sid, ref mut branches, _) => {
                    self.walk_simple_identifier(sid);
                    for &mut (ref mut attrs, ref mut branch) in branches {
                        for attr in attrs {
                            self.walk_attribute(attr);
                        }
                        self.walk_use_tree(branch);
                    }
                }
                &mut UseTree::SuperBranch(ref mut branches, _) => {
                    for &mut (ref mut attrs, ref mut branch) in branches {
                        for attr in attrs {
                            self.walk_attribute(attr);
                        }
                        self.walk_use_tree(branch);
                    }
                }
            }
        }

        self.use_tree_post_fn.as_mut().map(|fun| fun(tree));
    }

    pub fn walk_type_def(&mut self, type_def: &mut TypeDef) {
        if self.type_def_pre_fn
               .as_mut()
               .map_or(true, |fun| fun(type_def)) {
            match type_def {
                &mut TypeDef::Alias(ref mut inner_type) => self.walk_type(inner_type),
                &mut TypeDef::TypeLevelFun(ref mut attrs, ref mut args, ref mut inner, _) => {
                    for attr in attrs {
                        self.walk_attribute(attr);
                    }
                    for &mut (ref mut attrs, ref mut sid) in args {
                        for attr in attrs {
                            self.walk_attribute(attr);
                        }
                        self.walk_simple_identifier(sid);
                    }
                    self.walk_type_def(inner);
                }
                &mut TypeDef::Sum(_, ref mut attrs, ref mut summands, _) => {
                    for attr in attrs {
                        self.walk_attribute(attr);
                    }
                    for &mut (ref mut attrs, ref mut summand) in summands {
                        for attr in attrs {
                            self.walk_attribute(attr);
                        }
                        self.walk_summand(summand);
                    }
                }
            }
        }

        self.type_def_post_fn.as_mut().map(|fun| fun(type_def));
    }

    pub fn walk_summand(&mut self, summand: &mut Summand) {
        if self.summand_pre_fn
               .as_mut()
               .map_or(true, |fun| fun(summand)) {
            match summand {
                &mut Summand::Empty(ref mut sid, _) => self.walk_simple_identifier(sid),
                &mut Summand::Anon(ref mut sid, ref mut types, _) => {
                    self.walk_simple_identifier(sid);
                    for _type in types {
                        self.walk_type(_type);
                    }
                }
                &mut Summand::Named(ref mut sid, ref mut triples, _) => {
                    self.walk_simple_identifier(sid);
                    for &mut (ref mut attrs, ref mut sid, ref mut _type) in triples {
                        for attr in attrs {
                            self.walk_attribute(attr);
                        }
                        self.walk_simple_identifier(sid);
                        self.walk_type(_type);
                    }
                }
            }
        }

        self.summand_post_fn.as_mut().map(|fun| fun(summand));
    }

    pub fn walk_type(&mut self, _type: &mut Type) {
        if self.type_pre_fn.as_mut().map_or(true, |fun| fun(_type)) {
            match _type {
                &mut Type::Id(ref mut attrs, ref mut id, _) => {
                    for attr in attrs {
                        self.walk_attribute(attr);
                    }
                    self.walk_identifier(id);
                }
                &mut Type::MacroInv(ref mut attrs, ref mut inv, _) => {
                    for attr in attrs {
                        self.walk_attribute(attr);
                    }
                    self.walk_macro_invocation(inv);
                }
                &mut Type::Ptr(ref mut attrs, ref mut inner, _) |
                &mut Type::PtrMut(ref mut attrs, ref mut inner, _) |
                &mut Type::Array(ref mut attrs, ref mut inner, _) => {
                    for attr in attrs {
                        self.walk_attribute(attr);
                    }
                    self.walk_type(inner.as_mut());
                }
                &mut Type::ProductRepeated(ref mut attrs, ref mut inner, ref mut rep, _) => {
                    for attr in attrs {
                        self.walk_attribute(attr);
                    }
                    self.walk_type(inner.as_mut());
                    self.walk_repetition(rep);
                }
                &mut Type::ProductAnon(ref mut attrs, ref mut inners, _) => {
                    for attr in attrs {
                        self.walk_attribute(attr);
                    }
                    for inner in inners {
                        self.walk_type(inner);
                    }
                }
                &mut Type::ProductNamed(ref mut attrs, ref mut triples, _) => {
                    for attr in attrs {
                        self.walk_attribute(attr);
                    }
                    for &mut (ref mut attrs, ref mut sid, ref mut _type) in triples {
                        for attr in attrs {
                            self.walk_attribute(attr);
                        }
                        self.walk_simple_identifier(sid);
                        self.walk_type(_type);
                    }
                }
                &mut Type::FunAnon(ref mut attrs, ref mut args, ref mut ret_type, _) => {
                    for attr in attrs {
                        self.walk_attribute(attr);
                    }
                    for arg in args {
                        self.walk_type(arg);
                    }
                    self.walk_type(ret_type.as_mut());
                }
                &mut Type::FunNamed(ref mut attrs, ref mut triples, ref mut ret_type, _) => {
                    for attr in attrs {
                        self.walk_attribute(attr);
                    }
                    for &mut (ref mut attrs, ref mut sid, ref mut _type) in triples {
                        for attr in attrs {
                            self.walk_attribute(attr);
                        }
                        self.walk_simple_identifier(sid);
                        self.walk_type(_type);
                    }
                    self.walk_type(ret_type.as_mut());
                }
                &mut Type::TypeApplicationAnon(ref mut attrs, ref mut id, ref mut args, _) => {
                    for attr in attrs {
                        self.walk_attribute(attr);
                    }
                    self.walk_identifier(id);
                    for arg in args {
                        self.walk_type(arg);
                    }
                }
                &mut Type::TypeApplicationNamed(ref mut attrs, ref mut id, ref mut triples, _) => {
                    for attr in attrs {
                        self.walk_attribute(attr);
                    }
                    self.walk_identifier(id);
                    for &mut (ref mut attrs, ref mut sid, ref mut _type) in triples {
                        for attr in attrs {
                            self.walk_attribute(attr);
                        }
                        self.walk_simple_identifier(sid);
                        self.walk_type(_type);
                    }
                }
            }
        }

        self.type_post_fn.as_mut().map(|fun| fun(_type));
    }

    pub fn walk_repetition(&mut self, rep: &mut Repetition) {
        if self.repetition_pre_fn
               .as_mut()
               .map_or(true, |fun| fun(rep)) {
            match rep {
                &mut Repetition::Literal(_, _) => {}
                &mut Repetition::Macro(ref mut inv) => self.walk_macro_invocation(inv),
            }
        }

        self.repetition_post_fn.as_mut().map(|fun| fun(rep));
    }

    pub fn walk_macro_invocation(&mut self, inv: &mut MacroInvocation) {
        if self.macro_invocation_pre_fn
               .as_mut()
               .map_or(true, |fun| fun(inv)) {
            self.walk_identifier(&mut inv.0);
        }

        self.macro_invocation_post_fn
            .as_mut()
            .map(|fun| fun(inv));
    }

    pub fn walk_identifier(&mut self, id: &mut Identifier) {
        if self.identifier_pre_fn
               .as_mut()
               .map_or(true, |fun| fun(id)) {
            for sid in id.0.iter_mut() {
                self.walk_simple_identifier(sid);
            }
        }

        self.identifier_post_fn.as_mut().map(|fun| fun(id));
    }

    pub fn walk_pattern(&mut self, pattern: &mut Pattern) {
        if self.pattern_pre_fn
               .as_mut()
               .map_or(true, |fun| fun(pattern)) {
            match pattern {
                &mut Pattern::Blank(_) => {}
                &mut Pattern::Id(_, ref mut sid, ref mut annotation, _) => {
                    self.walk_simple_identifier(sid);
                    annotation
                        .as_mut()
                        .map_or((), |_type| self.walk_type(_type));
                }
                &mut Pattern::Literal(ref mut lit) => self.walk_literal(lit),
                &mut Pattern::Ptr(ref mut inner, _) => self.walk_pattern(inner.as_mut()),
                &mut Pattern::ProductAnon(ref mut inners, _) => {
                    for &mut (ref mut attrs, ref mut inner) in inners {
                        for attr in attrs {
                            self.walk_attribute(attr);
                        }
                        self.walk_pattern(inner);
                    }
                }
                &mut Pattern::ProductNamed(ref mut triples, _) => {
                    for &mut (ref mut attrs, ref mut sid, ref mut inner) in triples {
                        for attr in attrs {
                            self.walk_attribute(attr);
                        }
                        self.walk_simple_identifier(sid);
                        self.walk_pattern(inner);
                    }
                }
                &mut Pattern::SummandEmpty(ref mut sid, _) => self.walk_simple_identifier(sid),
                &mut Pattern::SummandAnon(ref mut sid, ref mut inners, _) => {
                    self.walk_simple_identifier(sid);
                    for &mut (ref mut attrs, ref mut inner) in inners {
                        for attr in attrs {
                            self.walk_attribute(attr);
                        }
                        self.walk_pattern(inner);
                    }
                }
                &mut Pattern::SummandNamed(ref mut sid, ref mut triples, _) => {
                    self.walk_simple_identifier(sid);
                    for &mut (ref mut attrs, ref mut sid, ref mut inner) in triples {
                        for attr in attrs {
                            self.walk_attribute(attr);
                        }
                        self.walk_simple_identifier(sid);
                        self.walk_pattern(inner);
                    }
                }
            }
        }

        self.pattern_post_fn.as_mut().map(|fun| fun(pattern));
    }

    pub fn walk_expression(&mut self, exp: &mut Expression) {
        if self.expression_pre_fn
               .as_mut()
               .map_or(true, |fun| fun(exp)) {
            match exp {
                &mut Expression::Id(ref mut attrs, ref mut id, _) => {
                    for attr in attrs {
                        self.walk_attribute(attr);
                    }
                    self.walk_identifier(id);
                }
                &mut Expression::Literal(ref mut attrs, ref mut lit, _) => {
                    for attr in attrs {
                        self.walk_attribute(attr);
                    }
                    self.walk_literal(lit);
                }
                &mut Expression::MacroInv(ref mut attrs, ref mut inv, _) => {
                    for attr in attrs {
                        self.walk_attribute(attr);
                    }
                    self.walk_macro_invocation(inv);
                }
                &mut Expression::Ref(ref mut attrs, ref mut inner, _) |
                &mut Expression::RefMut(ref mut attrs, ref mut inner, _) |
                &mut Expression::Deref(ref mut attrs, ref mut inner, _) |
                &mut Expression::DerefMut(ref mut attrs, ref mut inner, _) |
                &mut Expression::Array(ref mut attrs, ref mut inner, _) => {
                    for attr in attrs {
                        self.walk_attribute(attr);
                    }
                    self.walk_expression(inner.as_mut());
                }
                &mut Expression::ArrayIndex(ref mut attrs, ref mut inner, ref mut index, _) => {
                    for attr in attrs {
                        self.walk_attribute(attr);
                    }
                    self.walk_expression(inner.as_mut());
                    self.walk_expression(index.as_mut());
                }
                &mut Expression::ProductRepeated(ref mut attrs, ref mut inner, ref mut rep, _) => {
                    for attr in attrs {
                        self.walk_attribute(attr);
                    }
                    self.walk_expression(inner.as_mut());
                    self.walk_repetition(rep);
                }
                &mut Expression::ProductAnon(ref mut attrs, ref mut inners, _) => {
                    for attr in attrs {
                        self.walk_attribute(attr);
                    }
                    for inner in inners {
                        self.walk_expression(inner);
                    }
                }
                &mut Expression::ProductNamed(ref mut attrs, ref mut triples, _) => {
                    for attr in attrs {
                        self.walk_attribute(attr);
                    }
                    for &mut (ref mut attrs, ref mut sid, ref mut exp) in triples {
                        for attr in attrs {
                            self.walk_attribute(attr);
                        }
                        self.walk_simple_identifier(sid);
                        self.walk_expression(exp);
                    }
                }
                &mut Expression::ProductAccessAnon(ref mut attrs,
                                                   ref mut inner,
                                                   ref mut lit,
                                                   _) => {
                    for attr in attrs {
                        self.walk_attribute(attr);
                    }
                    self.walk_expression(inner.as_mut());
                    self.walk_literal(lit);
                }
                &mut Expression::ProductAccessNamed(ref mut attrs,
                                                    ref mut inner,
                                                    ref mut sid,
                                                    _) => {
                    for attr in attrs {
                        self.walk_attribute(attr);
                    }
                    self.walk_expression(inner.as_mut());
                    self.walk_simple_identifier(sid);
                }
                &mut Expression::FunLiteral(ref mut attrs,
                                            ref mut args,
                                            ref mut ret_type,
                                            ref mut body,
                                            _) => {
                    for attr in attrs {
                        self.walk_attribute(attr);
                    }
                    for &mut (ref mut attrs, ref mut pattern) in args {
                        for attr in attrs {
                            self.walk_attribute(attr);
                        }
                        self.walk_pattern(pattern);
                    }
                    self.walk_type(ret_type);
                    for exp in body {
                        self.walk_expression(exp);
                    }
                }
                &mut Expression::FunApplicationAnon(ref mut attrs,
                                                    ref mut fun,
                                                    ref mut args,
                                                    _) => {
                    for attr in attrs {
                        self.walk_attribute(attr);
                    }
                    self.walk_expression(fun.as_mut());
                    for exp in args {
                        self.walk_expression(exp);
                    }
                }
                &mut Expression::FunApplicationNamed(ref mut attrs,
                                                     ref mut fun,
                                                     ref mut triples,
                                                     _) => {
                    for attr in attrs {
                        self.walk_attribute(attr);
                    }
                    self.walk_expression(fun.as_mut());
                    for &mut (ref mut attrs, ref mut sid, ref mut exp) in triples {
                        for attr in attrs {
                            self.walk_attribute(attr);
                        }
                        self.walk_simple_identifier(sid);
                        self.walk_expression(exp);
                    }
                }
                &mut Expression::Generic(ref mut attrs, ref mut args, ref mut exp, _) => {
                    for attr in attrs {
                        self.walk_attribute(attr);
                    }
                    for &mut (ref mut attrs, ref mut sid) in args {
                        for attr in attrs {
                            self.walk_attribute(attr);
                        }
                        self.walk_simple_identifier(sid);
                    }
                    self.walk_expression(exp.as_mut());
                }
                &mut Expression::TypeApplicationAnon(ref mut attrs,
                                                     ref mut id,
                                                     ref mut args,
                                                     _) => {
                    for attr in attrs {
                        self.walk_attribute(attr);
                    }
                    self.walk_identifier(id);
                    for arg in args {
                        self.walk_type(arg);
                    }
                }
                &mut Expression::TypeApplicationNamed(ref mut attrs,
                                                      ref mut id,
                                                      ref mut triples,
                                                      _) => {
                    for attr in attrs {
                        self.walk_attribute(attr);
                    }
                    self.walk_identifier(id);
                    for &mut (ref mut attrs, ref mut sid, ref mut _type) in triples {
                        for attr in attrs {
                            self.walk_attribute(attr);
                        }
                        self.walk_simple_identifier(sid);
                        self.walk_type(_type);
                    }
                }
                &mut Expression::Cast(ref mut attrs, ref mut inner, ref mut _type, _) => {
                    for attr in attrs {
                        self.walk_attribute(attr);
                    }
                    self.walk_expression(inner.as_mut());
                    self.walk_type(_type);
                }
                &mut Expression::LAnd(ref mut attrs, ref mut lhs, ref mut rhs, _) |
                &mut Expression::LOr(ref mut attrs, ref mut lhs, ref mut rhs, _) => {
                    for attr in attrs {
                        self.walk_attribute(attr);
                    }
                    self.walk_expression(lhs.as_mut());
                    self.walk_expression(rhs.as_mut());
                }
                &mut Expression::Assignment(ref mut attrs, ref mut assignee, ref mut val, _) => {
                    for attr in attrs {
                        self.walk_attribute(attr);
                    }
                    self.walk_expression(assignee.as_mut());
                    self.walk_expression(val.as_mut());
                }
                &mut Expression::Val(ref mut attrs, ref mut pattern, ref mut rhs, _) => {
                    for attr in attrs {
                        self.walk_attribute(attr);
                    }
                    self.walk_pattern(pattern);
                    rhs.as_mut().map_or((), |val| self.walk_expression(val));
                }
                &mut Expression::If(ref mut attrs,
                                    ref mut cond,
                                    ref mut if_exprs,
                                    ref mut else_exprs,
                                    _) => {
                    for attr in attrs {
                        self.walk_attribute(attr);
                    }
                    self.walk_expression(cond.as_mut());
                    for exp in if_exprs {
                        self.walk_expression(exp);
                    }
                    match else_exprs {
                        &mut Some(ref mut exprs) => {
                            for exp in exprs {
                                self.walk_expression(exp);
                            }
                        }
                        &mut None => {}
                    }
                }
                &mut Expression::While(ref mut attrs, ref mut cond, ref mut block, _) => {
                    for attr in attrs {
                        self.walk_attribute(attr);
                    }
                    self.walk_expression(cond.as_mut());
                    for exp in block {
                        self.walk_expression(exp);
                    }
                }
                &mut Expression::Case(ref mut attrs, ref mut exp, ref mut branches, _) |
                &mut Expression::Loop(ref mut attrs, ref mut exp, ref mut branches, _) => {
                    for attr in attrs {
                        self.walk_attribute(attr);
                    }
                    self.walk_expression(exp.as_mut());
                    for &mut (ref mut pattern, ref mut body) in branches {
                        self.walk_pattern(pattern);
                        for exp in body {
                            self.walk_expression(exp);
                        }
                    }
                }
                &mut Expression::Return(ref mut attrs, ref mut exp, _) |
                &mut Expression::Break(ref mut attrs, ref mut exp, _) => {
                    for attr in attrs {
                        self.walk_attribute(attr);
                    }
                    exp.as_mut()
                        .map_or((), |val| self.walk_expression(val.as_mut()));
                }
            }
        }

        self.expression_post_fn.as_mut().map(|fun| fun(exp));
    }

    pub fn walk_ffi_language(&mut self, lang: &mut FfiLanguage) {
        self.ffi_language_fn.as_mut().map(|fun| fun(lang));
    }

    pub fn walk_ffi_item(&mut self, ffi_item: &mut FfiItem) {
        if self.ffi_item_pre_fn
               .as_mut()
               .map_or(true, |fun| fun(ffi_item)) {
            match ffi_item {
                &mut FfiItem::Type(_, ref mut sid, _) => self.walk_simple_identifier(sid),
                &mut FfiItem::Val(_, ref mut sid, ref mut _type, _) => {
                    self.walk_simple_identifier(sid);
                    self.walk_type(_type);
                }
            }
        }

        self.ffi_item_post_fn.as_mut().map(|fun| fun(ffi_item));
    }
}
