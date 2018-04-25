// use std::collections::HashMap;
//
// use ast::*;
// use ast_walker::AstWalkerMut;
//
// const CC: &'static str = "cc";
// const NOT: &'static str = "not";
// const ANY: &'static str = "any";
// const ALL: &'static str = "all";
//
// pub enum CcError {
//     NotArgsItem(usize, usize),
//     MultipleArgs(usize, usize),
//     NonStringFeature(usize, usize),
//     InnerLitArg(usize, usize),
//     InvalidInnerAttribute(usize, usize),
//     MultipleArgsOnNot(usize, usize),
// }
//
// /// Takes an ast and a set of features for conditional compilation, then removes all conditional
// /// compilation attributes from the ast, dropping all code without the given features.
// ///
// /// Afterwards, there are no more cond attributes in the ast. This way, later stages of the
// /// compiler don't need to know about conditional compilation at all. There are some drawbacks to
// /// that, but it is easy to implement for the bootstrap compiler.
// pub fn filter_conditionals<'i>(file: &mut File<'i>,
//                                features: &HashMap<String, String>)
//                                -> Vec<CcError> {
//     let mut walker = AstWalkerMut::new();
//     let mut errs = vec![];
//
//     walker.file_pre_fn = Some(Box::new(|file| {
//         let mut new_file = vec![];
//
//         for &(ref attrs, ref item) in file.0.iter() {
//             match should_stay(attrs, features) {
//                 Ok(true) => new_file.push((attrs.clone(), item.clone())),
//                 Ok(false) => {}
//                 Err(err) => errs.push(err),
//             }
//         }
//
//         *file = File(new_file);
//         return true; // continue running the walker on the new file
//     }));
//
//     walker.walk_file(file);
//     errs
// }
//
// // fn filter_file<'i>(file: &mut File<'i>, features: &HashMap<String, String>) -> Option<CcError<'i>> {
// //     let mut new_file = vec![];
// //
// //     for &(ref attrs, ref item) in file.0.iter() {
// //         match should_stay(attrs, features) {
// //             Ok(true) => new_file.push((attrs.clone(), item.clone())),
// //             Ok(false) => {}
// //             Err(err) => return Some(err),
// //         }
// //     }
// //
// //     *file = File(new_file);
// //     for &mut (_, ref mut item) in file.0.iter_mut() {
// //         if let Some(err) = filter_item(item, features) {
// //             return Some(err);
// //         }
// //     }
// //
// //     return None;
// // }
// //
// // fn filter_item<'i>(item: &mut Item<'i>, features: &HashMap<String, String>) -> Option<CcError<'i>> {
// //     match item {
// //         &mut Item::Use(_, _, ref mut use_tree, _) => filter_use_tree(use_tree, features),
// //         &mut Item::Type(_, _, ref mut type_def, _) => filter_type_def(type_def, features),
// //         _ => unimplemented!(),
// //     }
// // }
// //
// // fn filter_use_tree<'i>(use_tree: &mut UseTree<'i>,
// //                        features: &HashMap<String, String>)
// //                        -> Option<CcError<'i>> {
// //     match use_tree {
// //         &mut UseTree::IdLeaf(_, _) |
// //         &mut UseTree::SelfLeaf(_) |
// //         &mut UseTree::IdRenamedLeaf(_, _, _) |
// //         &mut UseTree::SelfRenamedLeaf(_, _) => return None,
// //         &mut UseTree::IdBranch(_, ref mut inner, _) |
// //         &mut UseTree::SuperBranch(ref mut inner, _) => {
// //             let mut new_inner = vec![];
// //
// //             for &(ref attrs, ref tree) in inner.iter() {
// //                 match should_stay(attrs, features) {
// //                     Ok(true) => new_inner.push((attrs.clone(), tree.clone())),
// //                     Ok(false) => {}
// //                     Err(err) => return Some(err),
// //                 }
// //             }
// //
// //             *inner = new_inner;
// //             for &mut (_, ref mut tree) in inner.iter_mut() {
// //                 if let Some(err) = filter_use_tree(tree, features) {
// //                     return Some(err);
// //                 }
// //             }
// //
// //             return None;
// //         }
// //     }
// // }
// //
// // fn filter_type_def<'i>(type_def: &mut TypeDef<'i>,
// //                        features: &HashMap<String, String>)
// //                        -> Option<CcError<'i>> {
// //     unimplemented!()
// // }
// //
// fn should_stay<'i>(attrs: &Vec<Attribute<'i>>,
//                    features: &HashMap<String, String>)
//                    -> Result<bool, CcError> {
//     for attr in attrs {
//         if attr.0.sid().as_str() == CC {
//             return check_cc(&attr.0, features);
//         }
//     }
//
//     // no cc attribute, so keep it by default
//     return Ok(true);
// }
//
// // Checks a cc attribute
// fn check_cc<'i>(meta: &MetaItem<'i>, features: &HashMap<String, String>) -> Result<bool, CcError> {
//     debug_assert!(meta.sid().as_str() == CC);
//     match meta {
//         &MetaItem::Nullary(_, ref pair) |
//         &MetaItem::Pair(_, _, ref pair) |
//         &MetaItem::LitArg(_, _, ref pair) => {
//             let span = pair.clone().into_span();
//             return Err(CcError::NotArgsItem(span.start(), span.end()));
//         }
//         &MetaItem::Args(_, ref inner, ref pair) => {
//             if inner.len() > 1 {
//                 let span = pair.clone().into_span();
//                 return Err(CcError::MultipleArgs(span.start(), span.end()));
//             } else {
//                 return check_inner(inner.get(0).unwrap(), features);
//             }
//         }
//     }
// }
//
// // Checks an attribute that is nested below a cc attribute
// fn check_inner<'i>(meta: &MetaItem<'i>,
//                    features: &HashMap<String, String>)
//                    -> Result<bool, CcError> {
//     match meta {
//         &MetaItem::Nullary(ref sid, _) => return Ok(features.contains_key(sid.as_str())),
//         &MetaItem::Pair(ref sid, ref lit, ref pair) => {
//             match lit {
//                 &Literal::String(ref feature, _) => {
//                     return Ok(features
//                                   .get(sid.as_str())
//                                   .map_or(false, |val| val == feature));
//                 }
//                 _ => {
//                     let span = pair.clone().into_span();
//                     return Err(CcError::NonStringFeature(span.start(), span.end()));
//                 }
//             }
//         }
//         &MetaItem::LitArg(_, _, ref pair) => {
//             let span = pair.clone().into_span();
//             return Err(CcError::InnerLitArg(span.start(), span.end()));
//         }
//         &MetaItem::Args(ref sid, ref args, ref pair) => {
//             match sid.as_str() {
//                 NOT => {
//                     if args.len() > 1 {
//                         let span = pair.clone().into_span();
//                         return Err(CcError::MultipleArgsOnNot(span.start(), span.end()));
//                     } else {
//                         return check_inner(args.get(0).unwrap(), features).map(|stay| !stay);
//                     }
//                 }
//                 ANY => {
//                     let mut stay = false;
//
//                     for item in args.iter() {
//                         match check_inner(item, features) {
//                             Err(err) => return Err(err),
//                             Ok(true) => stay = true,
//                             Ok(false) => {}
//                         }
//                     }
//
//                     return Ok(stay);
//                 }
//                 ALL => {
//                     let mut stay = true;
//
//                     for item in args.iter() {
//                         match check_inner(item, features) {
//                             Err(err) => return Err(err),
//                             Ok(false) => stay = false,
//                             Ok(true) => {}
//                         }
//                     }
//
//                     return Ok(stay);
//                 }
//                 other => {
//                     let span = pair.clone().into_span();
//                     return Err(CcError::InvalidInnerAttribute(span.start(), span.end()));
//                 }
//             }
//         }
//     }
// }
//
// // list of cc attributes that could be set by the compiler (see https://doc.rust-lang.org/reference/attributes.html#conditional-compilation):
// // - target_arch
// // - target_os
// // - target_family
// // - target_endian
// // - target_pointer_width
