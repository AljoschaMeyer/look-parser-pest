//! AST nodes for look, but also with references to the concrete syntax.

use std::str::FromStr;

use pest::{Span, Error, Parser, iterators::Pair};

use super::{Rule, LookParser, unescape::unescape};

pub type PestResult<'i, N> = Result<N, Error<'i, Rule>>;

#[derive(Debug, PartialEq, Eq)]
pub struct SimpleIdentifier<'i>(pub Span<'i>);

impl<'i> SimpleIdentifier<'i> {
    pub fn as_str(&self) -> &str {
        self.0.as_str()
    }
}

fn pair_to_simple_identifier<'i>(p: Pair<'i, Rule>) -> SimpleIdentifier<'i> {
    debug_assert!(p.as_rule() == Rule::sid);
    SimpleIdentifier(p.into_span())
}

pub fn p_sid<'i>(input: &'i str) -> PestResult<SimpleIdentifier<'i>> {
    LookParser::parse(Rule::sid, input).map(|mut pairs| pair_to_simple_identifier(pairs.next().unwrap()))
}

#[test]
fn test_sid() {
    assert_eq!(p_sid("abc").unwrap().as_str(), "abc");
    assert_eq!(p_sid("__").unwrap().as_str(), "__");
    assert_eq!(p_sid("_9").unwrap().as_str(), "_9");
    assert_eq!(p_sid("a_b").unwrap().as_str(), "a_b");
    assert_eq!(p_sid("_a").unwrap().as_str(), "_a");
    assert_eq!(p_sid("a_").unwrap().as_str(), "a_");
    assert_eq!(p_sid("abcdefghABCDEFGHabcdefghABCDEFGHabcdefghABCDEFGHabcdefghABCDEFGHabcdefghABCDEFGHabcdefghABCDEFGHabcdefghABCDEFGHabcdefghABCDEFG").unwrap().as_str(), "abcdefghABCDEFGHabcdefghABCDEFGHabcdefghABCDEFGHabcdefghABCDEFGHabcdefghABCDEFGHabcdefghABCDEFGHabcdefghABCDEFGHabcdefghABCDEFG");

    assert!(p_sid("").is_err());
    assert!(p_sid("_").is_err());
    assert!(p_sid("abcdefghABCDEFGHabcdefghABCDEFGHabcdefghABCDEFGHabcdefghABCDEFGHabcdefghABCDEFGHabcdefghABCDEFGHabcdefghABCDEFGHabcdefghABCDEFGH").is_err());
    assert!(p_sid("_bcdefghABCDEFGHabcdefghABCDEFGHabcdefghABCDEFGHabcdefghABCDEFGHabcdefghABCDEFGHabcdefghABCDEFGHabcdefghABCDEFGHabcdefghABCDEFGH").is_err());
    assert!(p_sid("use").is_err());
    assert!(p_sid("mod").is_err());
    assert!(p_sid("self").is_err());
    assert!(p_sid("super").is_err());
    assert!(p_sid("deps").is_err());
    assert!(p_sid("magic").is_err());
    assert!(p_sid("goto").is_err());
    assert!(p_sid("label").is_err());
    assert!(p_sid("break").is_err());
    assert!(p_sid("return").is_err());
    assert!(p_sid("while").is_err());
    assert!(p_sid("match").is_err());
    assert!(p_sid("if").is_err());
    assert!(p_sid("then").is_err());
    assert!(p_sid("else").is_err());
    assert!(p_sid("let").is_err());
    assert!(p_sid("as").is_err());
    assert!(p_sid("type").is_err());
    assert!(p_sid("macro").is_err());
    assert!(p_sid("mut").is_err());
    assert!(p_sid("pub").is_err());
}

#[derive(Debug, PartialEq, Eq)]
pub struct Identifier<'i>(pub Vec<SimpleIdentifier<'i>>, pub Pair<'i, Rule>);

fn pair_to_identifier<'i>(pair: Pair<'i, Rule>) -> Identifier<'i> {
    let mut p = pair.clone().into_inner();

    let first_sid = p.next().unwrap();
    debug_assert!(first_sid.as_rule() == Rule::sid);
    let mut ids = vec![SimpleIdentifier(first_sid.into_span())];

    loop {
        match p.next() {
            None => return Identifier(ids, pair),
            Some(scope) => {
                debug_assert!(scope.as_rule() == Rule::scope);
                let sid = p.next().unwrap();
                debug_assert!(sid.as_rule() == Rule::sid);
                ids.push(SimpleIdentifier(sid.into_span()));
            }
        }
    }
}

pub fn p_id<'i>(input: &'i str) -> PestResult<Identifier<'i>> {
    LookParser::parse(Rule::id, input).map(|mut pairs| pair_to_identifier(pairs.next().unwrap()))
}

#[test]
fn test_id() {
    let id = p_id("abc:: \n  _d  :: __ :: _89").unwrap();
    let mut id_iter = id.0.iter();

    assert_eq!(id_iter.next().unwrap().as_str(), "abc");
    assert_eq!(id_iter.next().unwrap().as_str(), "_d");
    assert_eq!(id_iter.next().unwrap().as_str(), "__");
    assert_eq!(id_iter.next().unwrap().as_str(), "_89");
    assert!(id_iter.next().is_none());
}

#[derive(Debug, PartialEq)]
pub enum Literal<'i> {
    Int(u64, Pair<'i, Rule>),
    Float(f64, Pair<'i, Rule>),
    String(String, Pair<'i, Rule>),
}
impl<'i> Eq for Literal<'i> {} // float literals are never NaN, Inf or -Inf

fn pair_to_literal<'i>(p: Pair<'i, Rule>) -> Literal<'i> {
    debug_assert!(p.as_rule() == Rule::literal);
    let pair = p.into_inner().next().unwrap();

    match pair.as_rule() {
        Rule::dec_int => {
            let mut digits: Vec<u8> = vec![];
            digits.extend(pair.as_str().as_bytes());
            digits.retain(|byte| *byte != 95);
            let int = u64::from_str_radix(unsafe {
                                          &String::from_utf8_unchecked(digits)
                                      }, 10).unwrap();
            Literal::Int(int, pair)
        }
        Rule::bin_int => {
            let mut digits: Vec<u8> = vec![];
            digits.extend(pair.as_str()[2..].as_bytes());
            digits.retain(|byte| *byte != 95);
            let int = u64::from_str_radix(unsafe {
                                          &String::from_utf8_unchecked(digits)
                                      }, 2).unwrap();
            Literal::Int(int, pair)
        }
        Rule::hex_int => {
            let mut digits: Vec<u8> = vec![];
            digits.extend(pair.as_str()[2..].as_bytes());
            digits.retain(|byte| *byte != 95);
            let int = u64::from_str_radix(unsafe {
                                          &String::from_utf8_unchecked(digits)
                                      }, 16).unwrap();
            Literal::Int(int, pair)
        }
        Rule::float => {
            let mut digits: Vec<u8> = vec![];
            digits.extend(pair.as_str().as_bytes());
            digits.retain(|byte| *byte != 95);
            let float = f64::from_str(unsafe {
                                          &String::from_utf8_unchecked(digits)
                                      }).unwrap();
            Literal::Float(float, pair)
        }
        Rule::string => {
            let total_chars = pair.as_str().len();
            let mut unescaped = unescape(&pair.as_str()[1..total_chars - 1]).unwrap();

            Literal::String(unescaped, pair)
        }
        _ => unreachable!()
    }
}

pub fn p_literal<'i>(input: &'i str) -> PestResult<Literal<'i>> {
    LookParser::parse(Rule::literal, input).map(|mut pairs| pair_to_literal(pairs.next().unwrap()))
}

#[cfg(test)]
fn test_int_lit(src: &str, expected: u64) {
    match p_literal(src).unwrap() {
        Literal::Int(int, _) => assert_eq!(int, expected),
        _ => panic!()
    }
}

#[cfg(test)]
fn test_float_lit(src: &str, expected: f64) {
    match p_literal(src).unwrap() {
        Literal::Float(float, _) => assert_eq!(float, expected),
        _ => panic!()
    }
}

#[cfg(test)]
fn test_string_lit(src: &str, expected: &str) {
    match p_literal(src).unwrap() {
        Literal::String(string, _) => assert_eq!(string, expected),
        _ => panic!()
    }
}

#[test]
fn test_literal() {
    test_int_lit("0", 0);
    test_int_lit("12345", 12345);
    test_int_lit("123_123", 123_123);
    test_int_lit("1_", 1);
    test_int_lit("0b_01_10__", 0b_01_10__);
    test_int_lit("0x_AF__123_", 0x_AF__123_);

    test_float_lit("1.2", 1.2);
    test_float_lit("1.2e3", 1.2e3);
    test_float_lit("1.2e+3", 1.2e+3);
    test_float_lit("1.2e-3", 1.2e-3);
    test_float_lit("1_._12_e+__3__5_", 1_.12_E+__3__5_);

    test_string_lit(r#""""#, "");
    test_string_lit(r#""a""#, "a");
    test_string_lit(r#""'""#, "'");
    test_string_lit(r#""abc""#, "abc");
    test_string_lit(r#""öäü""#, "öäü");
    test_string_lit(r#""💂🏾""#, "💂🏾");
    test_string_lit(r#""\"""#, "\"");
    test_string_lit(r#""\\""#, "\\");
    test_string_lit(r#""\n""#, "\n");
    test_string_lit(r#""\t""#, "\t");
    test_string_lit(r#""\0""#, "\0");
    test_string_lit(r#""\u09AF""#, "\u{09AF}");
}

#[derive(Debug, PartialEq, Eq)]
pub enum MetaItem<'i> {
    Nullary(SimpleIdentifier<'i>, Pair<'i, Rule>),
    Pair(SimpleIdentifier<'i>, Literal<'i>, Pair<'i, Rule>),
    LitArg(SimpleIdentifier<'i>, Literal<'i>, Pair<'i, Rule>),
    Args(SimpleIdentifier<'i>, Vec<MetaItem<'i>>, Pair<'i, Rule>),
}

fn pair_to_meta_item<'i>(p: Pair<'i, Rule>) -> MetaItem<'i> {
    debug_assert!(p.as_rule() == Rule::meta_item);
    let pair = p.clone().into_inner().next().unwrap();

    match pair.as_rule() {
        Rule::meta_item_nullary => {
            MetaItem::Nullary(pair_to_simple_identifier(pair.into_inner().next().unwrap()), p)
        }
        Rule::meta_item_pair => {
            let mut pairs = pair.into_inner();
            MetaItem::Pair(pair_to_simple_identifier(pairs.next().unwrap()), pair_to_literal(pairs.next().unwrap()), p)
        }
        Rule::meta_item_lit_arg => {
            let mut pairs = pair.into_inner();
            MetaItem::LitArg(pair_to_simple_identifier(pairs.next().unwrap()), pair_to_literal(pairs.next().unwrap()), p)
        }
        Rule::meta_item_args => {
            let mut pairs = pair.into_inner();
            let sid = pair_to_simple_identifier(pairs.next().unwrap());
            let inner = pairs.map(pair_to_meta_item).collect();
            MetaItem::Args(sid, inner, p)
        }
        _ => unreachable!()
    }
}

pub fn p_meta_item<'i>(input: &'i str) -> PestResult<MetaItem<'i>> {
    LookParser::parse(Rule::meta_item, input).map(|mut pairs| pair_to_meta_item(pairs.next().unwrap()))
}

#[test]
fn test_meta_item() {
    match p_meta_item("abc").unwrap() {
        MetaItem::Nullary(sid, _) => assert_eq!(sid.as_str(), "abc"),
        _ => panic!()
    }

    match p_meta_item("abc = 12.34").unwrap() {
        MetaItem::Pair(sid, Literal::Float(float, _), _) => {
            assert_eq!(sid.as_str(), "abc");
            assert_eq!(float, 12.34);
        },
        _ => panic!()
    }

    match p_meta_item("abc(12.34)").unwrap() {
        MetaItem::LitArg(sid, Literal::Float(float, _), _) => {
            assert_eq!(sid.as_str(), "abc");
            assert_eq!(float, 12.34);
        },
        _ => panic!()
    }

    match p_meta_item("a(b = 42 , c(d = 12.34))").unwrap() {
            MetaItem::Args(ref sid, ref args, _) => {
                assert_eq!(sid.as_str(), "a");
                match args[0] {
                    MetaItem::Pair(ref sid, Literal::Int(int, _), _) => {
                        assert_eq!(sid.as_str(), "b");
                        assert_eq!(int, 42);
                    }
                    _ => panic!(),
                }

                match args[1] {
                    MetaItem::Args(ref sid, ref args, _) => {
                        assert_eq!(sid.as_str(), "c");
                        match args[0] {
                            MetaItem::Pair(ref sid, Literal::Float(float, _), _) => {
                                assert_eq!(sid.as_str(), "d");
                                assert_eq!(float, 12.34);
                            }
                            _ => panic!(),
                        }
                    }
                    _ => panic!(),
                }
            }
            _ => panic!(),
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct Attribute<'i>(MetaItem<'i>, Pair<'i, Rule>);

fn pair_to_attribute<'i>(p: Pair<'i, Rule>) -> Attribute<'i> {
    debug_assert!(p.as_rule() == Rule::attribute);
    let pair = p.clone().into_inner().next().unwrap();
    Attribute(pair_to_meta_item(pair), p)
}

pub fn p_attribute<'i>(input: &'i str) -> PestResult<Attribute<'i>> {
    LookParser::parse(Rule::attribute, input).map(|mut pairs| pair_to_attribute(pairs.next().unwrap()))
}

#[test]
fn test_attribute() {
    match p_attribute("#[abc]").unwrap().0 {
        MetaItem::Nullary(sid, _) => assert_eq!(sid.as_str(), "abc"),
        _ => panic!()
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct MacroInvocation<'i>(Identifier<'i>, &'i str, Pair<'i, Rule>);

fn pair_to_macro_invocation<'i>(p: Pair<'i, Rule>) -> MacroInvocation<'i> {
    debug_assert!(p.as_rule() == Rule::macro_invocation);
    let mut pairs = p.clone().into_inner();
    MacroInvocation(pair_to_identifier(pairs.next().unwrap()), pairs.next().unwrap().as_str(), p)
}

pub fn p_macro_invocation<'i>(input: &'i str) -> PestResult<MacroInvocation<'i>> {
    LookParser::parse(Rule::macro_invocation, input).map(|mut pairs| pair_to_macro_invocation(pairs.next().unwrap()))
}

#[test]
fn test_macro_invocation() {
    let inv = p_macro_invocation("$foo()").unwrap();
    assert_eq!((inv.0).0[0].as_str(), "foo");
    assert_eq!(inv.1, "");

    let inv = p_macro_invocation("$bar(())").unwrap();
    assert_eq!((inv.0).0[0].as_str(), "bar");
    assert_eq!(inv.1, "()");

    let inv = p_macro_invocation("$baz( a , : ])").unwrap();
    assert_eq!((inv.0).0[0].as_str(), "baz");
    assert_eq!(inv.1, " a , : ]");

    assert!(p_macro_invocation("a(()").is_err());
}

#[derive(Debug, PartialEq, Eq)]
pub enum Repetition<'i> {
    Literal(u64, Pair<'i, Rule>),
    Macro(MacroInvocation<'i>),
}

fn pair_to_repetition<'i>(p: Pair<'i, Rule>) -> Repetition<'i> {
    debug_assert!(p.as_rule() == Rule::repetition);
    let pair = p.clone().into_inner().next().unwrap();

    match pair.as_rule() {
        Rule::dec_int => {
            let mut digits: Vec<u8> = vec![];
            digits.extend(pair.as_str().as_bytes());
            digits.retain(|byte| *byte != 95);
            let int = u64::from_str_radix(unsafe {
                                          &String::from_utf8_unchecked(digits)
                                      }, 10).unwrap();
            Repetition::Literal(int, pair)
        }
        Rule::bin_int => {
            let mut digits: Vec<u8> = vec![];
            digits.extend(pair.as_str()[2..].as_bytes());
            digits.retain(|byte| *byte != 95);
            let int = u64::from_str_radix(unsafe {
                                          &String::from_utf8_unchecked(digits)
                                      }, 2).unwrap();
            Repetition::Literal(int, pair)
        }
        Rule::hex_int => {
            let mut digits: Vec<u8> = vec![];
            digits.extend(pair.as_str()[2..].as_bytes());
            digits.retain(|byte| *byte != 95);
            let int = u64::from_str_radix(unsafe {
                                          &String::from_utf8_unchecked(digits)
                                      }, 16).unwrap();
            Repetition::Literal(int, pair)
        }
        Rule::macro_invocation => {
            Repetition::Macro(pair_to_macro_invocation(pair))
        }
        _ => unreachable!()
    }
}

pub fn p_repetition<'i>(input: &'i str) -> PestResult<Repetition<'i>> {
    LookParser::parse(Rule::repetition, input).map(|mut pairs| pair_to_repetition(pairs.next().unwrap()))
}

#[test]
fn test_repetition() {
    match p_repetition("42").unwrap() {
        Repetition::Literal(int, _) => {
            assert_eq!(int, 42);
        }
        _ => panic!()
    }

    match p_repetition("0b10").unwrap() {
        Repetition::Literal(int, _) => {
            assert_eq!(int, 0b10);
        }
        _ => panic!()
    }

    match p_repetition("0x123").unwrap() {
        Repetition::Literal(int, _) => {
            assert_eq!(int, 0x123);
        }
        _ => panic!()
    }

    match p_repetition("$foo()").unwrap() {
        Repetition::Macro(inv) => {
            assert_eq!((inv.0).0[0].as_str(), "foo");
            assert_eq!(inv.1, "");
        }
        _ => panic!()
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum Type<'i> {
    Id(Vec<Attribute<'i>>, Identifier<'i>, Pair<'i, Rule>),
    MacroInv(Vec<Attribute<'i>>, MacroInvocation<'i>, Pair<'i, Rule>),
    Ptr(Vec<Attribute<'i>>, Box<Type<'i>>, Pair<'i, Rule>),
    PtrMut(Vec<Attribute<'i>>, Box<Type<'i>>, Pair<'i, Rule>),
    Array(Vec<Attribute<'i>>, Box<Type<'i>>, Pair<'i, Rule>),
    ProductRepeated(Vec<Attribute<'i>>, Box<Type<'i>>, Repetition<'i>, Pair<'i, Rule>),
    ProductAnon(Vec<Attribute<'i>>, Vec<Type<'i>>, Pair<'i, Rule>),
    ProductNamed(Vec<Attribute<'i>>, Vec<(Vec<Attribute<'i>>, SimpleIdentifier<'i>, Type<'i>)>, Pair<'i, Rule>),
    FunAnon(Vec<Attribute<'i>>, Vec<Type<'i>>, Box<Type<'i>>, Pair<'i, Rule>),
    FunNamed(Vec<Attribute<'i>>, Vec<(Vec<Attribute<'i>>, SimpleIdentifier<'i>, Type<'i>)>, Box<Type<'i>>, Pair<'i, Rule>),
    TypeApplicationAnon(Vec<Attribute<'i>>, Identifier<'i>, Vec<Type<'i>>, Pair<'i, Rule>),
    TypeApplicationNamed(Vec<Attribute<'i>>,
                         Identifier<'i>,
                         Vec<(Vec<Attribute<'i>>, SimpleIdentifier<'i>, Type<'i>)>,
                         Pair<'i, Rule>),
}

impl<'i> Type<'i> {
    pub fn attributes(&self) -> &Vec<Attribute> {
        match self {
            &Type::Id(ref attrs, _, _) => attrs,
            &Type::MacroInv(ref attrs, _, _) => attrs,
            &Type::Ptr(ref attrs, _, _) => attrs,
            &Type::PtrMut(ref attrs, _, _) => attrs,
            &Type::Array(ref attrs, _, _) => attrs,
            &Type::ProductRepeated(ref attrs, _, _, _) => attrs,
            &Type::ProductAnon(ref attrs, _, _) => attrs,
            &Type::ProductNamed(ref attrs, _, _) => attrs,
            &Type::FunAnon(ref attrs, _, _, _) => attrs,
            &Type::FunNamed(ref attrs, _, _, _) => attrs,
            &Type::TypeApplicationAnon(ref attrs, _, _, _) => attrs,
            &Type::TypeApplicationNamed(ref attrs, _, _, _) => attrs,
        }
    }
}

fn pair_to_named_type_arg<'i>(p: Pair<'i, Rule>) -> (Vec<Attribute<'i>>, SimpleIdentifier<'i>, Type<'i>) {
    debug_assert!(p.as_rule() == Rule::named_type_arg);

    let mut attrs = vec![];

    for pair in p.into_inner() {
        match pair.as_rule() {
            Rule::attribute => {
                attrs.push(pair_to_attribute(pair));
            }

            Rule::actual_named_type_arg => {
                let mut pairs = pair.into_inner();
                let sid = pair_to_simple_identifier(pairs.next().unwrap());
                let _type = pair_to_type(pairs.next().unwrap());
                return (attrs, sid, _type)
            }

            _ => unreachable!()
        }
    }

    unreachable!()
}

fn pair_to_named_product_field<'i>(p: Pair<'i, Rule>) -> (Vec<Attribute<'i>>, SimpleIdentifier<'i>, Type<'i>) {
    debug_assert!(p.as_rule() == Rule::named_product_field);

    let mut attrs = vec![];

    for pair in p.into_inner() {
        match pair.as_rule() {
            Rule::attribute => {
                attrs.push(pair_to_attribute(pair));
            }

            Rule::actual_named_product_field => {
                let mut pairs = pair.into_inner();
                let sid = pair_to_simple_identifier(pairs.next().unwrap());
                let _type = pair_to_type(pairs.next().unwrap());
                return (attrs, sid, _type)
            }

            _ => unreachable!()
        }
    }

    unreachable!()
}

fn pair_to_type<'i>(p: Pair<'i, Rule>) -> Type<'i> {
    debug_assert!(p.as_rule() == Rule::_type);

    let mut attrs = vec![];

    for pair in p.clone().into_inner() {
        match pair.as_rule() {
            Rule::attribute => {
                attrs.push(pair_to_attribute(pair));
            }

            Rule::actual_type => {
                let pair = pair.into_inner().next().unwrap();

                match pair.as_rule() {
                    Rule::id => return Type::Id(attrs, pair_to_identifier(pair), p),

                    Rule::type_application_anon => {
                        let mut pairs = pair.into_inner();
                        let id = pair_to_identifier(pairs.next().unwrap());
                        let mut args = pairs.map(pair_to_type).collect();
                        return Type::TypeApplicationAnon(attrs, id, args, p);
                    }

                    Rule::type_application_named => {
                        let mut pairs = pair.into_inner();
                        let id = pair_to_identifier(pairs.next().unwrap());
                        let mut named_type_args = pairs.map(pair_to_named_type_arg).collect();
                        return Type::TypeApplicationNamed(attrs, id, named_type_args, p);
                    }

                    Rule::macro_invocation => {
                        return Type::MacroInv(attrs, pair_to_macro_invocation(pair), p)
                    }

                    Rule::ptr_type => {
                        return Type::Ptr(attrs, Box::new(pair_to_type(pair.into_inner().next().unwrap())), p)
                    }

                    Rule::ptr_mut_type => {
                        return Type::PtrMut(attrs, Box::new(pair_to_type(pair.into_inner().next().unwrap())), p)
                    }

                    Rule::array_type => {
                        return Type::Array(attrs, Box::new(pair_to_type(pair.into_inner().next().unwrap())), p)
                    }

                    Rule::product_repeated_type => {
                        let mut pairs = pair.into_inner();
                        return Type::ProductRepeated(attrs, Box::new(pair_to_type(pairs.next().unwrap())), pair_to_repetition(pairs.next().unwrap()), p);
                    }

                    Rule::product_anon_type => {
                        return Type::ProductAnon(attrs, pair.into_inner().map(pair_to_type).collect(), p);
                    }

                    Rule::product_named_type => {
                        let mut named_fields = pair.into_inner().map(pair_to_named_product_field).collect();
                        return Type::ProductNamed(attrs, named_fields, p);
                    }

                    Rule::fun_anon_type => {
                        let mut pairs = pair.into_inner();
                        let mut args = pairs.next().unwrap().into_inner().map(pair_to_type).collect();
                        let return_type = pair_to_type(pairs.next().unwrap());
                        return Type::FunAnon(attrs, args, Box::new(return_type), p);
                    }

                    Rule::fun_named_type => {
                        let mut pairs = pair.into_inner();
                        let mut args = pairs.next().unwrap().into_inner().map(pair_to_named_product_field).collect();
                        let return_type = pair_to_type(pairs.next().unwrap());
                        return Type::FunNamed(attrs, args, Box::new(return_type), p);
                    }

                    _ => unreachable!()
                }
            }

            _ => unreachable!()
        }
    }

    unreachable!()
}

pub fn p_type<'i>(input: &'i str) -> PestResult<Type<'i>> {
    LookParser::parse(Rule::_type, input).map(|mut pairs| pair_to_type(pairs.next().unwrap()))
}

#[cfg(test)]
fn assert_sid(sid: &SimpleIdentifier, expected: &str) {
    assert_eq!(sid.as_str(), expected);
}

#[cfg(test)]
fn assert_sid_id(id: &Identifier, expected: &str) {
    assert_sid(&id.0[0], expected);
}

#[cfg(test)]
fn assert_sid_type(t: &Type, expected: &str) {
    match t {
        &Type::Id(_, ref id, _) => {
            assert_eq!(id.0[0].as_str(), expected);
        }
        _ => panic!(),
    }
}

#[cfg(test)]
fn assert_sid_attr(attr: &Attribute, expected: &str) {
    match attr.0 {
        MetaItem::Nullary(ref sid, _) => {
            assert_sid(sid, expected);
        }
        _ => panic!(),
    }
}

#[test]
fn test_type() {
    assert_sid_type(&p_type("abc").unwrap(), "abc");

    match p_type("abc::def").unwrap() {
        Type::Id(attrs, id, _) => {
            assert_eq!(attrs, &[][..]);
            assert_eq!(id.0[0].as_str(), "abc");
            assert_eq!(id.0[1].as_str(), "def");
        }
        _ => panic!(),
    }

    let t = p_type("#[foo]{abc}").unwrap();
    assert_sid_attr(&t.attributes()[0], "foo");
    assert_sid_type(&t, "abc");

    let t = p_type("#[foo]#[bar]{abc}").unwrap();
    assert_sid_attr(&t.attributes()[0], "foo");
    assert_sid_attr(&t.attributes()[1], "bar");
    assert_sid_type(&t, "abc");

    match p_type("xyz<abc>").unwrap() {
        Type::TypeApplicationAnon(attrs, id, args, _) => {
            assert_eq!(attrs, &[][..]);
            assert_sid_id(&id, "xyz");
            assert_sid_type(&args[0], "abc");
        }
        _ => panic!(),
    }

    match p_type("xyz<abc, def>").unwrap() {
        Type::TypeApplicationAnon(attrs, id, args, _) => {
            assert_eq!(attrs, &[][..]);
            assert_sid_id(&id, "xyz");
            assert_sid_type(&args[0], "abc");
            assert_sid_type(&args[1], "def");
        }
        _ => panic!(),
    }

    match p_type("xyz<abc = def>").unwrap() {
        Type::TypeApplicationNamed(attrs, id, triples, _) => {
            assert_eq!(attrs, &[][..]);
            assert_sid_id(&id, "xyz");
            assert_eq!(triples[0].0, &[][..]);
            assert_sid(&triples[0].1, "abc");
            assert_sid_type(&triples[0].2, "def");
        }
        _ => panic!(),
    }

    match p_type("xyz<abc = def, ghi = jkl>").unwrap() {
        Type::TypeApplicationNamed(attrs, id, triples, _) => {
            assert_eq!(attrs, &[][..]);
            assert_sid_id(&id, "xyz");
            assert_eq!(triples[0].0, &[][..]);
            assert_sid(&triples[0].1, "abc");
            assert_sid_type(&triples[0].2, "def");
            assert_eq!(triples[1].0, &[][..]);
            assert_sid(&triples[1].1, "ghi");
            assert_sid_type(&triples[1].2, "jkl");
        }
        _ => panic!(),
    }

    match p_type("xyz<#[foo]{abc}>").unwrap() {
        Type::TypeApplicationAnon(attrs, id, args, _) => {
            assert_eq!(attrs, &[][..]);
            assert_sid_id(&id, "xyz");
            assert_sid_type(&args[0], "abc");
        }
        _ => panic!(),
    }

    match p_type("xyz<#[foo]{abc = def}>").unwrap() {
        Type::TypeApplicationNamed(attrs, id, triples, _) => {
            assert_eq!(attrs, &[][..]);
            assert_sid_id(&id, "xyz");
            assert_sid_attr(&triples[0].0[0], "foo");
            assert_sid(&triples[0].1, "abc");
            assert_sid_type(&triples[0].2, "def");
        }
        _ => panic!(),
    }

    match p_type("xyz<#[foo]#[bar]{abc = def}>").unwrap() {
        Type::TypeApplicationNamed(attrs, id, triples, _) => {
            assert_eq!(attrs, &[][..]);
            assert_sid_id(&id, "xyz");
            assert_sid_attr(&triples[0].0[0], "foo");
            assert_sid_attr(&triples[0].0[1], "bar");
            assert_sid(&triples[0].1, "abc");
            assert_sid_type(&triples[0].2, "def");
        }
        _ => panic!(),
    }

    match p_type("$abc()").unwrap() {
        Type::MacroInv(attrs, MacroInvocation(id, _, _), _) => {
            assert_eq!(attrs, &[][..]);
            assert_eq!(id.0[0].as_str(), "abc");
        }
        _ => panic!(),
    }

    match p_type("$abc::def()").unwrap() {
        Type::MacroInv(attrs, MacroInvocation(id, _, _), _) => {
            assert_eq!(attrs, &[][..]);
            assert_eq!(id.0[0].as_str(), "abc");
            assert_eq!(id.0[1].as_str(), "def");
        }
        _ => panic!(),
    }

    match p_type("@abc").unwrap() {
        Type::Ptr(attrs, inner, _) => {
            assert_eq!(attrs, &[][..]);
            assert_sid_type(&inner, "abc");
        }
        _ => panic!(),
    }

    match p_type("~abc").unwrap() {
        Type::PtrMut(attrs, inner, _) => {
            assert_eq!(attrs, &[][..]);
            assert_sid_type(&inner, "abc");
        }
        _ => panic!(),
    }

    match p_type("[abc]").unwrap() {
        Type::Array(attrs, inner, _) => {
            assert_eq!(attrs, &[][..]);
            assert_sid_type(&inner, "abc");
        }
        _ => panic!(),
    }

    match p_type("(abc; 42)").unwrap() {
        Type::ProductRepeated(attrs, inner, rep, _) => {
            assert_eq!(attrs, &[][..]);
            assert_sid_type(&inner, "abc");
            match rep {
                Repetition::Literal(int, _) => assert_eq!(int, 42),
                _ => panic!(),
            }
        }
        _ => panic!(),
    }

    match p_type("()").unwrap() {
        Type::ProductAnon(attrs, types, _) => {
            assert_eq!(attrs, &[][..]);
            assert_eq!(types, &[][..]);
        }
        _ => panic!(),
    }

    match p_type("(abc)").unwrap() {
        Type::ProductAnon(attrs, types, _) => {
            assert_eq!(attrs, &[][..]);
            assert_sid_type(&types[0], "abc");
        }
        _ => panic!(),
    }

    match p_type("(abc, def)").unwrap() {
        Type::ProductAnon(attrs, types, _) => {
            assert_eq!(attrs, &[][..]);
            assert_sid_type(&types[0], "abc");
            assert_sid_type(&types[1], "def");
        }
        _ => panic!(),
    }

    match p_type("(abc: def)").unwrap() {
        Type::ProductNamed(attrs, triples, _) => {
            assert_eq!(attrs, &[][..]);
            assert_eq!(triples[0].0, &[][..]);
            assert_sid(&triples[0].1, "abc");
            assert_sid_type(&triples[0].2, "def");
        }
        _ => panic!(),
    }

    match p_type("(abc: def, ghi: jkl)").unwrap() {
        Type::ProductNamed(attrs, triples, _) => {
            assert_eq!(attrs, &[][..]);
            assert_eq!(triples[0].0, &[][..]);
            assert_sid(&triples[0].1, "abc");
            assert_sid_type(&triples[0].2, "def");
            assert_eq!(triples[1].0, &[][..]);
            assert_sid(&triples[1].1, "ghi");
            assert_sid_type(&triples[1].2, "jkl");
        }
        _ => panic!(),
    }

    match p_type("(#[foo]{abc: def})").unwrap() {
        Type::ProductNamed(attrs, triples, _) => {
            assert_eq!(attrs, &[][..]);
            assert_sid_attr(&triples[0].0[0], "foo");
            assert_sid(&triples[0].1, "abc");
            assert_sid_type(&triples[0].2, "def");
        }
        _ => panic!(),
    }

    match p_type("(#[foo]#[bar]{abc: def})").unwrap() {
        Type::ProductNamed(attrs, triples, _) => {
            assert_eq!(attrs, &[][..]);
            assert_sid_attr(&triples[0].0[0], "foo");
            assert_sid_attr(&triples[0].0[1], "bar");
            assert_sid(&triples[0].1, "abc");
            assert_sid_type(&triples[0].2, "def");
        }
        _ => panic!(),
    }

    match p_type("() -> xyz").unwrap() {
        Type::FunAnon(attrs, args, ret, _) => {
            assert_eq!(attrs, &[][..]);
            assert_eq!(args, &[][..]);
            assert_sid_type(&ret, "xyz");
        }
        _ => panic!(),
    }

    match p_type("(abc) -> xyz").unwrap() {
        Type::FunAnon(attrs, args, ret, _) => {
            assert_eq!(attrs, &[][..]);
            assert_sid_type(&args[0], "abc");
            assert_sid_type(&ret, "xyz");
        }
        _ => panic!(),
    }

    match p_type("(abc, def) -> xyz").unwrap() {
        Type::FunAnon(attrs, args, ret, _) => {
            assert_eq!(attrs, &[][..]);
            assert_sid_type(&args[0], "abc");
            assert_sid_type(&args[1], "def");
            assert_sid_type(&ret, "xyz");
        }
        _ => panic!(),
    }

    match p_type("(abc: def) -> xyz").unwrap() {
        Type::FunNamed(attrs, triples, ret, _) => {
            assert_eq!(attrs, &[][..]);
            assert_eq!(triples[0].0, &[][..]);
            assert_sid(&triples[0].1, "abc");
            assert_sid_type(&triples[0].2, "def");
            assert_sid_type(&ret, "xyz");
        }
        _ => panic!(),
    }

    match p_type("(abc: def, ghi: jkl) -> xyz").unwrap() {
        Type::FunNamed(attrs, triples, ret, _) => {
            assert_eq!(attrs, &[][..]);
            assert_eq!(triples[0].0, &[][..]);
            assert_sid(&triples[0].1, "abc");
            assert_sid_type(&triples[0].2, "def");
            assert_eq!(triples[1].0, &[][..]);
            assert_sid(&triples[1].1, "ghi");
            assert_sid_type(&triples[1].2, "jkl");
            assert_sid_type(&ret, "xyz");
        }
        _ => panic!(),
    }

    match p_type("(#[foo]{abc: def}) -> xyz").unwrap() {
        Type::FunNamed(attrs, triples, ret, _) => {
            assert_eq!(attrs, &[][..]);
            assert_sid_attr(&triples[0].0[0], "foo");
            assert_sid(&triples[0].1, "abc");
            assert_sid_type(&triples[0].2, "def");
            assert_sid_type(&ret, "xyz");
        }
        _ => panic!(),
    }

    match p_type("(#[foo]#[bar]{abc: def}) -> xyz").unwrap() {
        Type::FunNamed(attrs, triples, ret, _) => {
            assert_eq!(attrs, &[][..]);
            assert_sid_attr(&triples[0].0[0], "foo");
            assert_sid_attr(&triples[0].0[1], "bar");
            assert_sid(&triples[0].1, "abc");
            assert_sid_type(&triples[0].2, "def");
            assert_sid_type(&ret, "xyz");
        }
        _ => panic!(),
    }
}

#[derive(Debug, PartialEq, Eq)]
// Bool is whether the fields are public
pub enum Summand<'i> {
    Empty(bool, SimpleIdentifier<'i>, Pair<'i, Rule>),
    Anon(bool, SimpleIdentifier<'i>,  Vec<Type<'i>>, Pair<'i, Rule>),
    Named(bool, SimpleIdentifier<'i>, Vec<(Vec<Attribute<'i>>, SimpleIdentifier<'i>, Type<'i>)>, Pair<'i, Rule>),
}

#[derive(Debug, PartialEq, Eq)]
pub enum TypeDef<'i> {
    Alias(Type<'i>),
    TypeLevelFun(Vec<Attribute<'i>>, Vec<(Vec<Attribute<'i>>, SimpleIdentifier<'i>)>, Box<TypeDef<'i>>, Pair<'i, Rule>),
    // pub | pub A(Foo, Bar) | pub B | C(x: Foo)
    // Bool is whether the tag constructors are public
    Sum(bool, Vec<Attribute<'i>>, Vec<(Vec<Attribute<'i>>, Summand<'i>)>, Pair<'i, Rule>),
}

fn pair_to_type_level_arg<'i>(p: Pair<'i, Rule>) -> (Vec<Attribute<'i>>, SimpleIdentifier<'i>) {
    assert!(p.as_rule() == Rule::type_level_arg);

    let mut attrs = vec![];

    for pair in p.into_inner() {
        match pair.as_rule() {
            Rule::attribute => {
                attrs.push(pair_to_attribute(pair));
            }

            Rule::sid => {
                return (attrs, pair_to_simple_identifier(pair));
            }

            _ => unreachable!()
        }
    }

    unreachable!()
}

fn pair_to_actual_summand<'i>(p: Pair<'i, Rule>) -> Summand<'i> {
    assert!(p.as_rule() == Rule::actual_summand);

    let mut pairs = p.clone().into_inner().peekable();
    let public = pairs.peek().unwrap().as_rule() == Rule::_pub;

    if public {
        pairs.next();
    }

    let sid = pair_to_simple_identifier(pairs.next().unwrap());

    match pairs.next() {
        None => Summand::Empty(public, sid, p),

        Some(pair) => {
            match pair.as_rule() {
                Rule::product_anon_type => {
                    Summand::Anon(public, sid, pair.into_inner().map(pair_to_type).collect(), p)
                }

                Rule::product_named_type => {
                    Summand::Named(public, sid, pair.into_inner().map(pair_to_named_product_field).collect(), p)
                }

                _ => unreachable!()
            }
        }
    }
}

fn pair_to_summand<'i>(p: Pair<'i, Rule>) -> (Vec<Attribute<'i>>, Summand<'i>) {
    assert!(p.as_rule() == Rule::summand);

    let mut attrs = vec![];

    for pair in p.into_inner() {
        match pair.as_rule() {
            Rule::attribute => {
                attrs.push(pair_to_attribute(pair));
            }

            Rule::actual_summand => {
                return (attrs, pair_to_actual_summand(pair));
            }

            _ => unreachable!()
        }
    }

    unreachable!()
}

fn pair_to_type_def<'i>(p: Pair<'i, Rule>) -> TypeDef<'i> {
    debug_assert!(p.as_rule() == Rule::type_def);
    let pair = p.clone().into_inner().next().unwrap();

    match pair.as_rule() {
        Rule::_type => {
            TypeDef::Alias(pair_to_type(pair))
        }

        Rule::type_level_fun => {
            let mut attrs = vec![];

            for pair in pair.into_inner() {
                match pair.as_rule() {
                    Rule::attribute => {
                        attrs.push(pair_to_attribute(pair));
                    }

                    Rule::actual_type_level_fun => {
                        let mut args = vec![];

                        for pair in pair.into_inner() {
                            match pair.as_rule() {
                                Rule::type_level_arg => {
                                    args.push(pair_to_type_level_arg(pair));
                                }

                                Rule::type_def => {
                                    return TypeDef::TypeLevelFun(attrs, args, Box::new(pair_to_type_def(pair)), p);
                                }
                                _ => unreachable!(),
                            }
                        }
                        unreachable!()
                    }
                    _ => unreachable!(),
                }
            }

            unreachable!()
        }

        Rule::sum => {
            let mut pairs = pair.into_inner().peekable();

            let mut attrs = vec![];
            let mut public = false;
            let mut summands = vec![];

            for pair in pairs {
                match pair.as_rule() {
                    Rule::attribute => {
                        attrs.push(pair_to_attribute(pair));
                    }

                    Rule::_pub => {
                        public = true;
                    }

                    Rule::summand => {
                        summands.push(pair_to_summand(pair));
                    }

                    _ => unreachable!()
                }
            }
            return TypeDef::Sum(public, attrs, summands, p);
        }

        _ => unreachable!()
    }
}

pub fn p_type_def<'i>(input: &'i str) -> PestResult<TypeDef<'i>> {
    LookParser::parse(Rule::type_def, input).map(|mut pairs| pair_to_type_def(pairs.next().unwrap()))
}

#[cfg(test)]
fn assert_sid_type_def(t: &TypeDef, expected: &str) {
    match t {
        &TypeDef::Alias(ref inner) => {
            assert_sid_type(inner, expected);
        }
        _ => panic!(),
    }
}

#[test]
fn test_type_def() {
    match p_type_def("abc::def").unwrap() {
        TypeDef::Alias(Type::Id(attrs, id, _)) => {
            assert_eq!(attrs, &[][..]);
            assert_eq!(id.0[0].as_str(), "abc");
            assert_eq!(id.0[1].as_str(), "def");
        }
        _ => panic!()
    }

    match p_type_def("#[foo] { abc::def }").unwrap() {
        TypeDef::Alias(Type::Id(attrs, id, _)) => {
            assert_eq!(attrs.len(), 1);
            assert_eq!(id.0[0].as_str(), "abc");
            assert_eq!(id.0[1].as_str(), "def");
        }
        _ => panic!()
    }

    match p_type_def("<A> => abc").unwrap() {
        TypeDef::TypeLevelFun(attrs, args, ret, _) => {
            assert_eq!(attrs, &[][..]);
            assert_eq!(args.len(), 1);
            assert_eq!(args[0].0, &[][..]);
            assert_sid(&args[0].1, "A");
            assert_sid_type_def(ret.as_ref(), "abc");
        }
        _ => panic!()
    }

    match p_type_def("<A, B> => abc").unwrap() {
        TypeDef::TypeLevelFun(attrs, args, ret, _) => {
            assert_eq!(attrs, &[][..]);
            assert_eq!(args.len(), 2);
            assert_eq!(args[0].0, &[][..]);
            assert_sid(&args[0].1, "A");
            assert_eq!(args[1].0, &[][..]);
            assert_sid(&args[1].1, "B");
            assert_sid_type_def(ret.as_ref(), "abc");
        }
        _ => panic!()
    }

    match p_type_def("<#[foo] { A }> => abc").unwrap() {
        TypeDef::TypeLevelFun(attrs, args, ret, _) => {
            assert_eq!(attrs, &[][..]);
            assert_eq!(args.len(), 1);
            assert_eq!(args[0].0.len(), 1);
            assert_sid(&args[0].1, "A");
            assert_sid_type_def(ret.as_ref(), "abc");
        }
        _ => panic!()
    }

    match p_type_def("#[foo] { <A> => abc }").unwrap() {
        TypeDef::TypeLevelFun(attrs, args, ret, _) => {
            assert_eq!(attrs.len(), 1);
            assert_eq!(args.len(), 1);
            assert_eq!(args[0].0, &[][..]);
            assert_sid(&args[0].1, "A");
            assert_sid_type_def(ret.as_ref(), "abc");
        }
        _ => panic!()
    }

    match p_type_def("| A").unwrap() {
        TypeDef::Sum(public, attrs, summands, _) => {
            assert!(!public);
            assert_eq!(attrs, &[][..]);
            assert_eq!(summands.len(), 1);
            assert_eq!(summands[0].0, &[][..]);
            match summands[0].1 {
                Summand::Empty(public, ref sid, _) => {
                    assert!(!public);
                    assert_sid(sid, "A");
                }
                _ => panic!()
            }
        }
        _ => panic!()
    }

    match p_type_def("pub | A").unwrap() {
        TypeDef::Sum(public, attrs, summands, _) => {
            assert!(public);
            assert_eq!(attrs, &[][..]);
            assert_eq!(summands.len(), 1);
            assert_eq!(summands[0].0, &[][..]);
            match summands[0].1 {
                Summand::Empty(public, ref sid, _) => {
                    assert!(!public);
                    assert_sid(sid, "A");
                }
                _ => panic!()
            }
        }
        _ => panic!()
    }


    match p_type_def("#[foo] { pub | A }").unwrap() {
        TypeDef::Sum(public, attrs, summands, _) => {
            assert!(public);
            assert_eq!(attrs.len(), 1);
            assert_eq!(summands.len(), 1);
            assert_eq!(summands[0].0, &[][..]);
            match summands[0].1 {
                Summand::Empty(public, ref sid, _) => {
                    assert!(!public);
                    assert_sid(sid, "A");
                }
                _ => panic!()
            }
        }
        _ => panic!()
    }

    match p_type_def("pub #[foo] { | A }").unwrap() {
        TypeDef::Sum(public, attrs, summands, _) => {
            assert!(public);
            assert_eq!(attrs.len(), 0);
            assert_eq!(summands.len(), 1);
            assert_eq!(summands[0].0.len(), 1);
            match summands[0].1 {
                Summand::Empty(public, ref sid, _) => {
                    assert!(!public);
                    assert_sid(sid, "A");
                }
                _ => panic!()
            }
        }
        _ => panic!()
    }

    match p_type_def("| pub A").unwrap() {
        TypeDef::Sum(public, attrs, summands, _) => {
            assert!(!public);
            assert_eq!(attrs, &[][..]);
            assert_eq!(summands.len(), 1);
            assert_eq!(summands[0].0, &[][..]);
            match summands[0].1 {
                Summand::Empty(public, ref sid, _) => {
                    assert!(public);
                    assert_sid(sid, "A");
                }
                _ => panic!()
            }
        }
        _ => panic!()
    }

    match p_type_def("| A | B").unwrap() {
        TypeDef::Sum(public, attrs, summands, _) => {
            assert!(!public);
            assert_eq!(attrs, &[][..]);
            assert_eq!(summands.len(), 2);
            assert_eq!(summands[0].0, &[][..]);
            match summands[0].1 {
                Summand::Empty(public, ref sid, _) => {
                    assert!(!public);
                    assert_sid(sid, "A");
                }
                _ => panic!()
            }
            assert_eq!(summands[1].0, &[][..]);
            match summands[1].1 {
                Summand::Empty(public, ref sid, _) => {
                    assert!(!public);
                    assert_sid(sid, "B");
                }
                _ => panic!()
            }
        }
        _ => panic!()
    }

    match p_type_def("| A(B)").unwrap() {
        TypeDef::Sum(public, attrs, summands, _) => {
            assert!(!public);
            assert_eq!(attrs, &[][..]);
            assert_eq!(summands.len(), 1);
            assert_eq!(summands[0].0, &[][..]);
            match summands[0].1 {
                Summand::Anon(public, ref sid, ref types, _) => {
                    assert!(!public);
                    assert_sid(sid, "A");
                    assert_eq!(types.len(), 1);
                    assert_sid_type(&types[0], "B");
                }
                _ => panic!()
            }
        }
        _ => panic!()
    }

    match p_type_def("| A(b: C)").unwrap() {
        TypeDef::Sum(public, attrs, summands, _) => {
            assert!(!public);
            assert_eq!(attrs, &[][..]);
            assert_eq!(summands.len(), 1);
            assert_eq!(summands[0].0, &[][..]);
            match summands[0].1 {
                Summand::Named(public, ref sid, ref args, _) => {
                    assert!(!public);
                    assert_sid(sid, "A");
                    assert_eq!(args.len(), 1);
                }
                _ => panic!()
            }
        }
        _ => panic!()
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum Pattern<'i> {
    Blank(Pair<'i, Rule>),
    Id(bool, SimpleIdentifier<'i>, Option<Type<'i>>, Pair<'i, Rule>),
    Literal(Literal<'i>),
    Ptr(Box<Pattern<'i>>, Pair<'i, Rule>),
    ProductAnon(Vec<(Vec<Attribute<'i>>, Pattern<'i>)>, Pair<'i, Rule>),
    ProductNamed(Vec<(Vec<Attribute<'i>>, SimpleIdentifier<'i>, Pattern<'i>)>, Pair<'i, Rule>),
    SummandEmpty(SimpleIdentifier<'i>, Pair<'i, Rule>),
    SummandAnon(SimpleIdentifier<'i>, Vec<(Vec<Attribute<'i>>, Pattern<'i>)>, Pair<'i, Rule>),
    SummandNamed(SimpleIdentifier<'i>, Vec<(Vec<Attribute<'i>>, SimpleIdentifier<'i>, Pattern<'i>)>, Pair<'i, Rule>)
}

fn pair_to_annotated_named_pattern<'i>(p: Pair<'i, Rule>) -> (Vec<Attribute<'i>>, SimpleIdentifier<'i>, Pattern<'i>) {
    debug_assert!(p.as_rule() == Rule::maybe_annotated_named_pattern);

    let mut attrs = vec![];
    let mut sid = None;

    for pair in p.into_inner() {
        match pair.as_rule() {
            Rule::attribute => {
                attrs.push(pair_to_attribute(pair));
            }

            Rule::sid => {
                sid = Some(pair_to_simple_identifier(pair));
            }

            Rule::pattern => {
                return (attrs, sid.unwrap(), pair_to_pattern(pair));
            }

            _ => unreachable!()
        }
    }
    unreachable!()
}

fn pair_to_annotated_pattern<'i>(p: Pair<'i, Rule>) -> (Vec<Attribute<'i>>, Pattern<'i>) {
    debug_assert!(p.as_rule() == Rule::maybe_annotated_pattern);

    let mut attrs = vec![];

    for pair in p.into_inner() {
        match pair.as_rule() {
            Rule::attribute => {
                attrs.push(pair_to_attribute(pair));
            }

            Rule::pattern => {
                return (attrs, pair_to_pattern(pair));
            }

            _ => unreachable!()
        }
    }
    unreachable!()
}

fn pair_to_pattern<'i>(p: Pair<'i, Rule>) -> Pattern<'i> {
    debug_assert!(p.as_rule() == Rule::pattern);
    let pair = p.clone().into_inner().next().unwrap();

    match pair.as_rule() {
        Rule::blank_pattern => {
            Pattern::Blank(p)
        }

        Rule::literal => {
            Pattern::Literal(pair_to_literal(pair))
        }

        Rule::ptr_pattern => {
            Pattern::Ptr(Box::new(pair_to_pattern(pair.into_inner().next().unwrap())), p)
        }

        Rule::id_pattern => {
            let mut pairs = pair.into_inner().peekable();
            let mutable = pairs.peek().unwrap().as_rule() == Rule::_mut;

            if mutable {
                pairs.next();
            }

            let sid = pair_to_simple_identifier(pairs.next().unwrap());
            let type_annotation = match pairs.next() {
                None => None,
                Some(pair) => Some(pair_to_type(pair))
            };

            Pattern::Id(mutable, sid, type_annotation, p)
        }

        Rule::product_anon_pattern => {
            Pattern::ProductAnon(pair.into_inner().map(pair_to_annotated_pattern).collect(), p)
        }

        Rule::product_named_pattern => {
            Pattern::ProductNamed(pair.into_inner().map(pair_to_annotated_named_pattern).collect(), p)
        }

        Rule::summand_pattern => {
            let mut pairs = pair.into_inner();
            let sid = pair_to_simple_identifier(pairs.next().unwrap());

            match pairs.next() {
                None => Pattern::SummandEmpty(sid, p),

                Some(pair) => {
                    match pair.as_rule() {
                        Rule::product_anon_pattern => {
                            Pattern::SummandAnon(sid, pair.into_inner().map(pair_to_annotated_pattern).collect(), p)
                        }

                        Rule::product_named_pattern => {
                            Pattern::SummandNamed(sid, pair.into_inner().map(pair_to_annotated_named_pattern).collect(), p)
                        }

                        _ => unreachable!()
                    }
                }
            }
        }

        _ => unreachable!()
    }
}

pub fn p_pattern<'i>(input: &'i str) -> PestResult<Pattern<'i>> {
    LookParser::parse(Rule::pattern, input).map(|mut pairs| pair_to_pattern(pairs.next().unwrap()))
}

#[test]
fn test_pattern() {
    match p_pattern("_").unwrap() {
        Pattern::Blank(_) => {}
        _ => panic!()
    }

    match p_pattern("42").unwrap() {
        Pattern::Literal(Literal::Int(int, _)) => assert_eq!(int, 42),
        _ => panic!()
    }

    match p_pattern("_abc").unwrap() {
        Pattern::Id(mutable, sid, type_annotation, _) => {
            assert!(!mutable);
            assert_sid(&sid, "_abc");
            assert_eq!(type_annotation, None);
        }
        _ => panic!()
    }

    match p_pattern("mut abc").unwrap() {
        Pattern::Id(mutable, sid, type_annotation, _) => {
            assert!(mutable);
            assert_sid(&sid, "abc");
            assert_eq!(type_annotation, None);
        }
        _ => panic!()
    }

    match p_pattern("abc: T").unwrap() {
        Pattern::Id(mutable, sid, type_annotation, _) => {
            assert!(!mutable);
            assert_sid(&sid, "abc");
            assert_sid_type(&type_annotation.unwrap(), "T");
        }
        _ => panic!()
    }

    match p_pattern("@_").unwrap() {
        Pattern::Ptr(inner, _) => {
            match inner.as_ref() {
                &Pattern::Blank(_) => {},
                _ => panic!()
            }
        }
        _ => panic!()
    }

    match p_pattern("()").unwrap() {
        Pattern::ProductAnon(inner, _) => {
            assert_eq!(inner.len(), 0);
        }
        _ => panic!()
    }

    match p_pattern("(_)").unwrap() {
        Pattern::ProductAnon(inner, _) => {
            assert_eq!(inner.len(), 1);
            assert_eq!(inner[0].0.len(), 0);
        }
        _ => panic!()
    }

    match p_pattern("(_, _)").unwrap() {
        Pattern::ProductAnon(inner, _) => {
            assert_eq!(inner.len(), 2);
            assert_eq!(inner[0].0.len(), 0);
            assert_eq!(inner[1].0.len(), 0);
        }
        _ => panic!()
    }

    match p_pattern("(#[foo] { _ } )").unwrap() {
        Pattern::ProductAnon(inner, _) => {
            assert_eq!(inner.len(), 1);
            assert_eq!(inner[0].0.len(), 1);
        }
        _ => panic!()
    }

    match p_pattern("(#[foo] #[bar] { _ } )").unwrap() {
        Pattern::ProductAnon(inner, _) => {
            assert_eq!(inner.len(), 1);
            assert_eq!(inner[0].0.len(), 2);
        }
        _ => panic!()
    }

    match p_pattern("(abc = _)").unwrap() {
        Pattern::ProductNamed(inner, _) => {
            assert_eq!(inner.len(), 1);
            assert_eq!(inner[0].0.len(), 0);
            assert_sid(&inner[0].1, "abc");
        }
        _ => panic!()
    }

    match p_pattern("(abc = _, def = _)").unwrap() {
        Pattern::ProductNamed(inner, _) => {
            assert_eq!(inner.len(), 2);
            assert_eq!(inner[0].0.len(), 0);
            assert_sid(&inner[0].1, "abc");
            assert_eq!(inner[1].0.len(), 0);
            assert_sid(&inner[1].1, "def");
        }
        _ => panic!()
    }

    match p_pattern("(#[foo] { abc = _ } )").unwrap() {
        Pattern::ProductNamed(inner, _) => {
            assert_eq!(inner.len(), 1);
            assert_eq!(inner[0].0.len(), 1);
            assert_sid(&inner[0].1, "abc");
        }
        _ => panic!()
    }

    match p_pattern("(#[foo] #[bar] { abc = _ } )").unwrap() {
        Pattern::ProductNamed(inner, _) => {
            assert_eq!(inner.len(), 1);
            assert_eq!(inner[0].0.len(), 2);
            assert_sid(&inner[0].1, "abc");
        }
        _ => panic!()
    }

    match p_pattern("| abc").unwrap() {
        Pattern::SummandEmpty(sid, _) => {
            assert_sid(&sid, "abc");
        }
        _ => panic!()
    }

    match p_pattern("| abc(_)").unwrap() {
        Pattern::SummandAnon(sid, inner, _) => {
            assert_sid(&sid, "abc");
            assert_eq!(inner.len(), 1);
            assert_eq!(inner[0].0.len(), 0);
        }
        _ => panic!()
    }

    match p_pattern("| abc(d = _)").unwrap() {
        Pattern::SummandNamed(sid, inner, _) => {
            assert_sid(&sid, "abc");
            assert_eq!(inner.len(), 1);
            assert_eq!(inner[0].0.len(), 0);
            assert_sid(&inner[0].1, "d");
        }
        _ => panic!()
    }
}
