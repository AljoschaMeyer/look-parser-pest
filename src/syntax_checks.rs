use ast::*;

use ast_walker::AstWalkerMut;

pub enum PseudoSyntaxError {
    // usizes are start and end offset in the source str
    ProductAccessNonIntLiteral(usize, usize),
    FunLiteralNonIdPattern(usize, usize),
    FunLiteralUntypedPattern(usize, usize),
    NonFunGenericExpr(usize, usize),
    NonLValueAssignment(usize, usize),
    ExprValPatternRefutable(usize, usize),
    SelfUse(usize, usize),
    ItemValUntypedNonfunction(usize, usize),
    ItemValNonIdPattern(usize, usize),
}

/// Performs checks on the ast that could have been done in the syntax instead, but I was too lazy.
pub fn syntax_checks<'i>(file: &mut File<'i>) -> Vec<PseudoSyntaxError> {
    let mut walker = AstWalkerMut::new();
    let mut errs = vec![];

    walker.expression_pre_fn =
        Some(Box::new(|exp| match exp {
                          &mut Expression::ProductAccessAnon(_, _, ref lit, _) => {
                              match lit {
                                  &Literal::Int(_, _) => true,
                                  &Literal::Float(_, ref pair) |
                                  &Literal::String(_, ref pair) => {
            let span = pair.clone().into_span();
            errs.push(PseudoSyntaxError::ProductAccessNonIntLiteral(span.start(), span.end()));
            true
        }
                              }
                          }
                          &mut Expression::FunLiteral(_, ref args, _, _, ref pair) => {
            for &(_, ref pattern) in args {
                match pattern {
                    &Pattern::Id(_, _, Some(_), _) => {}
                    &Pattern::Id(_, _, None, _) => {
                        let span = pair.clone().into_span();
                        errs.push(PseudoSyntaxError::FunLiteralUntypedPattern(span.start(),
                                                                              span.end()));
                    }
                    other => {
                        let span = other.pair().clone().into_span();
                        errs.push(PseudoSyntaxError::FunLiteralNonIdPattern(span.start(),
                                                                            span.end()));
                    }
                }
            }
            true
        }
                          &mut Expression::Generic(_, _, ref exp, _) => {
            match exp.as_ref() {
                &Expression::FunLiteral(_, _, _, _, _) => {}
                other => {
                    let span = other.pair().clone().into_span();
                    errs.push(PseudoSyntaxError::NonFunGenericExpr(span.start(), span.end()));
                }
            }
            true
        }
                          &mut Expression::Assignment(_, ref lhs, _, _) => {
                              if lhs.as_ref().is_lvalue() {
                                  true
                              } else {
                                  let span = lhs.pair().clone().into_span();
                                  errs.push(PseudoSyntaxError::NonLValueAssignment(span.start(),
                                                                                   span.end()));
                                  true
                              }
                          }
                          &mut Expression::Val(_, ref lhs, _, _) => {
                              if lhs.is_refutable() {
                                  let span = lhs.pair().clone().into_span();
                                  errs.push(PseudoSyntaxError::ExprValPatternRefutable(span.start(),
                                                                                   span.end()));
                                  true
                              } else {
                                  true
                              }
                          }
                          _ => true,
                      }));

    walker.item_pre_fn = Some(Box::new(|item| match item {
                                           &mut Item::Use(_, ref prefix, ref tree, _) => {
                                               match prefix {
                                                   &UsePrefix::None => {
                                                       match tree {
                                                           &UseTree::SelfLeaf(pair) => {
        let span = pair.clone().into_span();
        errs.push(PseudoSyntaxError::SelfUse(span.start(), span.end()));
        true
    }
                                                           _ => true,
                                                       }
                                                   }
                                                   _ => true,
                                               }
                                           }
                                           &mut Item::Val(_, ref pattern, ref exp, _) => {
        let must_be_annotated = match exp {
            &Expression::FunLiteral(_, _, _, _, _) => false,
            _ => true,
        };

        match pattern {
            &Pattern::Id(_, _, Some(_), _) => {}
            &Pattern::Id(_, _, None, pair) => {
                let span = pair.clone().into_span();
                errs.push(PseudoSyntaxError::ItemValUntypedNonfunction(span.start(), span.end()));
            }
            other => {
                let span = other.pair().clone().into_span();
                errs.push(PseudoSyntaxError::ItemValNonIdPattern(span.start(), span.end()));
            }
        }

        true
    }
                                           _ => true,
                                       }));

    walker.walk_file(file);

    errs
}
