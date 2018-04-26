use std::collections::HashMap;
use std::cell::RefCell;

use ast::*;
use ast_walker::*;

const CC: &'static str = "cc";
const NOT: &'static str = "not";
const ANY: &'static str = "any";
const ALL: &'static str = "all";

pub enum CcError {
    NotArgsItem(usize, usize),
    MultipleArgs(usize, usize),
    NonStringFeature(usize, usize),
    InnerLitArg(usize, usize),
    InvalidInnerAttribute(usize, usize),
    MultipleArgsOnNot(usize, usize),
}

/// Takes an ast and a set of features for conditional compilation, then removes all conditional
/// compilation attributes from the ast, dropping all code without the given features.
///
/// Afterwards, there are no more cond attributes in the ast. This way, later stages of the
/// compiler don't need to know about conditional compilation at all. There are some drawbacks to
/// that, but it is easy to implement for the bootstrap compiler.
pub fn filter_conditionals<'i>(file: &mut File<'i>,
                               features: &HashMap<String, String>)
                               -> Vec<CcError> {
    let errs = RefCell::new(vec![]);

    {
        let mut walker = AstWalkerMut {
            file_pre_fn: |file: &mut File| {
                let mut new_file = vec![];

                for &(ref attrs, ref item) in file.0.iter() {
                    match should_stay(attrs, features) {
                        Ok(true) => new_file.push((attrs.clone(), item.clone())),
                        Ok(false) => {}
                        Err(err) => errs.borrow_mut().push(err),
                    }
                }

                *file = File(new_file);
                return true; // continue running the walker on the new file
            },
            file_post_fn: file_unit,

            attribute_pre_fn: attribute_true,
            attribute_post_fn: attribute_unit,

            item_pre_fn: |item: &mut Item| match item {
                &mut Item::FfiBlock(_, ref mut ffi_items, _) => {
                    let mut new_ffi_items = vec![];

                    for &(ref attrs, ref ffi_item) in ffi_items.iter() {
                        match should_stay(attrs, features) {
                            Ok(true) => {
                                new_ffi_items.push((attrs.clone(), ffi_item.clone()));
                            }
                            Ok(false) => {}
                            Err(err) => errs.borrow_mut().push(err),
                        }
                    }

                    *ffi_items = new_ffi_items;
                    true
                }
                _ => true,
            },
            item_post_fn: item_unit,

            use_prefix_fn: use_prefix_unit,

            use_tree_pre_fn: |use_tree: &mut UseTree| match use_tree {
                &mut UseTree::IdBranch(_, ref mut branches, _) |
                &mut UseTree::SuperBranch(ref mut branches, _) => {
                    let mut new_branches = vec![];

                    for &(ref attrs, ref branch) in branches.iter() {
                        match should_stay(attrs, features) {
                            Ok(true) => {
                                new_branches.push((attrs.clone(), branch.clone()));
                            }
                            Ok(false) => {}
                            Err(err) => errs.borrow_mut().push(err),
                        }
                    }

                    *branches = new_branches;
                    true
                }
                _ => false, // leafs can't have conditional compilation
            },
            use_tree_post_fn: use_tree_unit,

            simple_identifier_fn: simple_identifier_unit,

            type_def_pre_fn: |type_def: &mut TypeDef| match type_def {
                &mut TypeDef::TypeLevelFun(_, ref mut args, _, _) => {
                    let mut new_args = vec![];

                    for &(ref attrs, ref sid) in args.iter() {
                        match should_stay(attrs, features) {
                            Ok(true) => {
                                new_args.push((attrs.clone(), sid.clone()));
                            }
                            Ok(false) => {}
                            Err(err) => errs.borrow_mut().push(err),
                        }
                    }

                    *args = new_args;
                    true
                }
                &mut TypeDef::Sum(_, _, ref mut summands, _) => {
                    let mut new_summands = vec![];

                    for &(ref attrs, ref summand) in summands.iter() {
                        match should_stay(attrs, features) {
                            Ok(true) => {
                                new_summands.push((attrs.clone(), summand.clone()));
                            }
                            Ok(false) => {}
                            Err(err) => errs.borrow_mut().push(err),
                        }
                    }

                    *summands = new_summands;
                    true
                }
                _ => true,
            },
            type_def_post_fn: type_def_unit,

            pattern_pre_fn: |pattern: &mut Pattern| match pattern {
                &mut Pattern::ProductAnon(ref mut inners, _) |
                &mut Pattern::SummandAnon(_, ref mut inners, _) => {
                    let mut new_inners = vec![];

                    for &(ref attrs, ref pattern) in inners.iter() {
                        match should_stay(attrs, features) {
                            Ok(true) => {
                                new_inners.push((attrs.clone(), pattern.clone()));
                            }
                            Ok(false) => {}
                            Err(err) => errs.borrow_mut().push(err),
                        }
                    }

                    *inners = new_inners;
                    true
                }
                &mut Pattern::ProductNamed(ref mut triples, _) |
                &mut Pattern::SummandNamed(_, ref mut triples, _) => {
                    let mut new_triples = vec![];

                    for &(ref attrs, ref triple) in triples.iter() {
                        match should_stay(attrs, features) {
                            Ok(true) => {
                                new_triples.push((attrs.clone(), triple.clone()));
                            }
                            Ok(false) => {}
                            Err(err) => errs.borrow_mut().push(err),
                        }
                    }

                    *triples = new_triples;
                    true
                }
                _ => true,
            },
            pattern_post_fn: pattern_unit,

            expression_pre_fn: |exp: &mut Expression| match exp {
                unimplemented!()
                // &mut Item::FfiBlock(_, ref mut ffi_items, _) => {
                //     let mut new_ffi_items = vec![];
                //
                //     for &(ref attrs, ref ffi_item) in ffi_items.iter() {
                //         match should_stay(attrs, features) {
                //             Ok(true) => {
                //                 new_ffi_items.push((attrs.clone(), ffi_item.clone()));
                //             }
                //             Ok(false) => {}
                //             Err(err) => errs.borrow_mut().push(err),
                //         }
                //     }
                //
                //     *ffi_items = new_ffi_items;
                //     true
                // }
                // // TODO
                // _ => true,
            },
            expression_post_fn: expression_unit,

            ffi_language_fn: ffi_language_unit,

            ffi_item_pre_fn: ffi_item_true,
            ffi_item_post_fn: ffi_item_unit,

            type_pre_fn: type_true,
            type_post_fn: type_unit,

            summand_pre_fn: summand_true,
            summand_post_fn: summand_unit,

            identifier_pre_fn: identifier_true,
            identifier_post_fn: identifier_unit,

            literal_fn: literal_unit,

            macro_invocation_pre_fn: macro_invocation_true,
            macro_invocation_post_fn: macro_invocation_unit,

            repetition_pre_fn: repetition_true,
            repetition_post_fn: repetition_unit,

            meta_item_pre_fn: meta_item_true,
            meta_item_post_fn: meta_item_unit,
        };

        walker.walk_file(file);
    }

    errs.into_inner()
}

fn should_stay<'i>(attrs: &Vec<Attribute<'i>>,
                   features: &HashMap<String, String>)
                   -> Result<bool, CcError> {
    for attr in attrs {
        if attr.0.sid().as_str() == CC {
            return check_cc(&attr.0, features);
        }
    }

    // no cc attribute, so keep it by default
    return Ok(true);
}

// Checks a cc attribute
fn check_cc<'i>(meta: &MetaItem<'i>, features: &HashMap<String, String>) -> Result<bool, CcError> {
    debug_assert!(meta.sid().as_str() == CC);
    match meta {
        &MetaItem::Nullary(_, ref pair) |
        &MetaItem::Pair(_, _, ref pair) |
        &MetaItem::LitArg(_, _, ref pair) => {
            let span = pair.clone().into_span();
            return Err(CcError::NotArgsItem(span.start(), span.end()));
        }
        &MetaItem::Args(_, ref inner, ref pair) => {
            if inner.len() > 1 {
                let span = pair.clone().into_span();
                return Err(CcError::MultipleArgs(span.start(), span.end()));
            } else {
                return check_inner(inner.get(0).unwrap(), features);
            }
        }
    }
}

// Checks an attribute that is nested below a cc attribute
fn check_inner<'i>(meta: &MetaItem<'i>,
                   features: &HashMap<String, String>)
                   -> Result<bool, CcError> {
    match meta {
        &MetaItem::Nullary(ref sid, _) => return Ok(features.contains_key(sid.as_str())),
        &MetaItem::Pair(ref sid, ref lit, ref pair) => {
            match lit {
                &Literal::String(ref feature, _) => {
                    return Ok(features
                                  .get(sid.as_str())
                                  .map_or(false, |val| val == feature));
                }
                _ => {
                    let span = pair.clone().into_span();
                    return Err(CcError::NonStringFeature(span.start(), span.end()));
                }
            }
        }
        &MetaItem::LitArg(_, _, ref pair) => {
            let span = pair.clone().into_span();
            return Err(CcError::InnerLitArg(span.start(), span.end()));
        }
        &MetaItem::Args(ref sid, ref args, ref pair) => {
            match sid.as_str() {
                NOT => {
                    if args.len() > 1 {
                        let span = pair.clone().into_span();
                        return Err(CcError::MultipleArgsOnNot(span.start(), span.end()));
                    } else {
                        return check_inner(args.get(0).unwrap(), features).map(|stay| !stay);
                    }
                }
                ANY => {
                    let mut stay = false;

                    for item in args.iter() {
                        match check_inner(item, features) {
                            Err(err) => return Err(err),
                            Ok(true) => stay = true,
                            Ok(false) => {}
                        }
                    }

                    return Ok(stay);
                }
                ALL => {
                    let mut stay = true;

                    for item in args.iter() {
                        match check_inner(item, features) {
                            Err(err) => return Err(err),
                            Ok(false) => stay = false,
                            Ok(true) => {}
                        }
                    }

                    return Ok(stay);
                }
                _ => {
                    let span = pair.clone().into_span();
                    return Err(CcError::InvalidInnerAttribute(span.start(), span.end()));
                }
            }
        }
    }
}

// list of cc attributes that could be set by the compiler (see https://doc.rust-lang.org/reference/attributes.html#conditional-compilation):
// - target_arch
// - target_os
// - target_family
// - target_endian
// - target_pointer_width
