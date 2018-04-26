// use std::cell::RefCell;
//
// use ast::*;
// use ast_walker::*;
//
// pub enum PseudoSyntaxError {
//     // usizes are start and end offset in the source str
//     ProductAccessNonIntLiteral(usize, usize),
//     FunLiteralNonIdPattern(usize, usize),
//     FunLiteralUntypedPattern(usize, usize),
//     NonFunGenericExpr(usize, usize),
//     NonLValueAssignment(usize, usize),
//     ExprValPatternRefutable(usize, usize),
//     SelfUse(usize, usize),
//     ItemValUntypedNonfunction(usize, usize),
//     ItemValNonIdPattern(usize, usize),
// }
//
// /// Performs checks on the ast that could have been done in the syntax instead, but I was too lazy.
// pub fn syntax_checks<'i>(file: &mut File<'i>) -> Vec<PseudoSyntaxError> {
//     let errs = RefCell::new(vec![]);
//
//     {
//         let mut walker = AstWalkerMut {
//             file_pre_fn: file_true,
//             file_post_fn: file_unit,
//
//             attribute_pre_fn: attribute_true,
//             attribute_post_fn: attribute_unit,
//
//             item_pre_fn: |item: &mut Item| match item {
//                 &mut Item::Use(_, ref prefix, ref tree, _) => {
//                     match prefix {
//                         &UsePrefix::None => {
//                             match tree {
//                                 &UseTree::SelfLeaf(ref pair) => {
//                                     let span = pair.clone().into_span();
//                                     errs.borrow_mut()
//                                         .push(PseudoSyntaxError::SelfUse(span.start(), span.end()));
//                                     true
//                                 }
//                                 _ => true,
//                             }
//                         }
//                         _ => true,
//                     }
//                 }
//                 &mut Item::Val(_, ref pattern, ref exp, _) => {
//                     let must_be_annotated = match exp {
//                         &Expression::FunLiteral(_, _, _, _, _) => false,
//                         _ => true,
//                     };
//
//                     match pattern {
//                         &Pattern::Id(_, _, Some(_), _) => {}
//                         &Pattern::Id(_, _, None, ref pair) => {
//                             if must_be_annotated {
//                                 let span = pair.clone().into_span();
//                                 errs.borrow_mut().push(PseudoSyntaxError::ItemValUntypedNonfunction(span.start(),
//                                                                                    span.end()));
//                             }
//                         }
//                         other => {
//                             let span = other.pair().clone().into_span();
//                             errs.borrow_mut()
//                                 .push(PseudoSyntaxError::ItemValNonIdPattern(span.start(),
//                                                                              span.end()));
//                         }
//                     }
//
//                     true
//                 }
//                 _ => true,
//             },
//             item_post_fn: item_unit,
//
//             use_prefix_fn: use_prefix_unit,
//
//             use_tree_pre_fn: use_tree_true,
//             use_tree_post_fn: use_tree_unit,
//
//             simple_identifier_fn: simple_identifier_unit,
//
//             type_def_pre_fn: type_def_true,
//             type_def_post_fn: type_def_unit,
//
//             pattern_pre_fn: pattern_true,
//             pattern_post_fn: pattern_unit,
//
//             expression_pre_fn: |exp: &mut Expression| match exp {
//                 &mut Expression::ProductAccessAnon(_, _, ref lit, _) => {
//                     match lit {
//                         &Literal::Int(_, _) => true,
//                         &Literal::Float(_, ref pair) |
//                         &Literal::String(_, ref pair) => {
//                             let span = pair.clone().into_span();
//                             errs.borrow_mut()
//                                 .push(PseudoSyntaxError::ProductAccessNonIntLiteral(span.start(),
//                                                                                     span.end()));
//                             true
//                         }
//                     }
//                 }
//                 &mut Expression::FunLiteral(_, ref args, _, _, ref pair) => {
//                     for &(_, ref pattern) in args {
//                         match pattern {
//                             &Pattern::Id(_, _, Some(_), _) => {}
//                             &Pattern::Id(_, _, None, _) => {
//                                 let span = pair.clone().into_span();
//                                 errs.borrow_mut().push(PseudoSyntaxError::FunLiteralUntypedPattern(span.start(),
//                                                                                   span.end()));
//                             }
//                             other => {
//                                 let span = other.pair().clone().into_span();
//                                 errs.borrow_mut()
//                                     .push(PseudoSyntaxError::FunLiteralNonIdPattern(span.start(),
//                                                                                     span.end()));
//                             }
//                         }
//                     }
//                     true
//                 }
//                 &mut Expression::Generic(_, _, ref exp, _) => {
//                     match exp.as_ref() {
//                         &Expression::FunLiteral(_, _, _, _, _) => {}
//                         other => {
//                             let span = other.pair().clone().into_span();
//                             errs.borrow_mut()
//                                 .push(PseudoSyntaxError::NonFunGenericExpr(span.start(),
//                                                                            span.end()));
//                         }
//                     }
//                     true
//                 }
//                 &mut Expression::Assignment(_, ref lhs, _, _) => {
//                     if lhs.as_ref().is_lvalue() {
//                         true
//                     } else {
//                         let span = lhs.pair().clone().into_span();
//                         errs.borrow_mut()
//                             .push(PseudoSyntaxError::NonLValueAssignment(span.start(), span.end()));
//                         true
//                     }
//                 }
//                 &mut Expression::Val(_, ref lhs, _, _) => {
//                     if lhs.is_refutable() {
//                         let span = lhs.pair().clone().into_span();
//                         errs.borrow_mut()
//                             .push(PseudoSyntaxError::ExprValPatternRefutable(span.start(),
//                                                                              span.end()));
//                         true
//                     } else {
//                         true
//                     }
//                 }
//                 _ => true,
//             },
//             expression_post_fn: expression_unit,
//
//             ffi_language_fn: ffi_language_unit,
//
//             ffi_item_pre_fn: ffi_item_true,
//             ffi_item_post_fn: ffi_item_unit,
//
//             type_pre_fn: type_true,
//             type_post_fn: type_unit,
//
//             summand_pre_fn: summand_true,
//             summand_post_fn: summand_unit,
//
//             identifier_pre_fn: identifier_true,
//             identifier_post_fn: identifier_unit,
//
//             literal_fn: literal_unit,
//
//             macro_invocation_pre_fn: macro_invocation_true,
//             macro_invocation_post_fn: macro_invocation_unit,
//
//             repetition_pre_fn: repetition_true,
//             repetition_post_fn: repetition_unit,
//
//             meta_item_pre_fn: meta_item_true,
//             meta_item_post_fn: meta_item_unit,
//         };
//
//         walker.walk_file(file);
//     }
//
//     errs.into_inner()
// }
