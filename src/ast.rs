//! AST nodes for look, but also with references to the concrete syntax.

use std::str::FromStr;

use pest::{Span, Error, Parser, iterators::Pair};

use super::{Rule, LookParser, unescape::unescape};

pub type PestResult<'i, N> = Result<N, Error<'i, Rule>>;

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct SimpleIdentifier<'i>(pub Span<'i>);

impl<'i> SimpleIdentifier<'i> {
    pub fn as_str(&self) -> &str {
        self.0.as_str()
    }
}

fn pair_to_attrs_and_sid<'i>(p: Pair<'i, Rule>) -> (Vec<Attribute<'i>>, SimpleIdentifier<'i>) {
    debug_assert!(p.as_rule() == Rule::maybe_attributed_sid);

    let mut attrs = vec![];

    for pair in p.into_inner() {
        match pair.as_rule() {
            Rule::attribute => attrs.push(pair_to_attribute(pair)),
            Rule::sid => return (attrs, pair_to_simple_identifier(pair)),
            _ => unreachable!()
        }
    }

    unreachable!()
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
    assert!(p_sid("dep").is_err());
    assert!(p_sid("magic").is_err());
    assert!(p_sid("goto").is_err());
    assert!(p_sid("label").is_err());
    assert!(p_sid("break").is_err());
    assert!(p_sid("return").is_err());
    assert!(p_sid("loop").is_err());
    assert!(p_sid("case").is_err());
    assert!(p_sid("if").is_err());
    assert!(p_sid("else").is_err());
    assert!(p_sid("val").is_err());
    assert!(p_sid("as").is_err());
    assert!(p_sid("type").is_err());
    assert!(p_sid("macro").is_err());
    assert!(p_sid("mut").is_err());
    assert!(p_sid("pub").is_err());
    assert!(p_sid("ffi").is_err());
}

#[derive(Debug, PartialEq, Eq, Clone)]
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

#[derive(Debug, PartialEq, Clone)]
pub enum Literal<'i> {
    Int(u64, Pair<'i, Rule>),
    Float(f64, Pair<'i, Rule>),
    String(String, Pair<'i, Rule>),
}
impl<'i> Eq for Literal<'i> {} // float literals are never NaN, Inf or -Inf

impl<'i> Literal<'i> {
    pub fn pair(&self) -> &Pair<'i, Rule> {
        match self {
            &Literal::Int(_, ref pair) => pair,
            &Literal::Float(_, ref pair) => pair,
            &Literal::String(_, ref pair) => pair,
        }
    }
}

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

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum MetaItem<'i> {
    Nullary(SimpleIdentifier<'i>, Pair<'i, Rule>),
    Pair(SimpleIdentifier<'i>, Literal<'i>, Pair<'i, Rule>),
    LitArg(SimpleIdentifier<'i>, Literal<'i>, Pair<'i, Rule>),
    Args(SimpleIdentifier<'i>, Vec<MetaItem<'i>>, Pair<'i, Rule>),
}

impl<'i> MetaItem<'i> {
    pub fn sid(&self) -> &SimpleIdentifier<'i> {
        match self {
            &MetaItem::Nullary(ref sid, _) => sid,
            &MetaItem::Pair(ref sid, _, _) => sid,
            &MetaItem::LitArg(ref sid, _, _) => sid,
            &MetaItem::Args(ref sid, _, _) => sid,
        }
    }
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

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Attribute<'i>(pub MetaItem<'i>, pub Pair<'i, Rule>);

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

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct MacroInvocation<'i>(pub Identifier<'i>, pub  &'i str, pub Pair<'i, Rule>);

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

#[derive(Debug, PartialEq, Eq, Clone)]
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

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Type<'i> {
    Id(Identifier<'i>, Pair<'i, Rule>),
    MacroInv(MacroInvocation<'i>, Pair<'i, Rule>),
    Ptr(Box<Type<'i>>, Pair<'i, Rule>),
    PtrMut(Box<Type<'i>>, Pair<'i, Rule>),
    Array(Box<Type<'i>>, Pair<'i, Rule>),
    ProductRepeated(Box<Type<'i>>, Repetition<'i>, Pair<'i, Rule>),
    ProductAnon(Vec<(Vec<Attribute<'i>>, Type<'i>)>, Pair<'i, Rule>),
    ProductNamed(Vec<(Vec<Attribute<'i>>, SimpleIdentifier<'i>, Type<'i>)>, Pair<'i, Rule>),
    FunAnon(Vec<(Vec<Attribute<'i>>, Type<'i>)>, Box<Type<'i>>, Pair<'i, Rule>),
    FunNamed(Vec<(Vec<Attribute<'i>>, SimpleIdentifier<'i>, Type<'i>)>, Box<Type<'i>>, Pair<'i, Rule>),
    TypeApplicationAnon(Identifier<'i>, Vec<(Vec<Attribute<'i>>, Type<'i>)>, Pair<'i, Rule>),
    TypeApplicationNamed(Identifier<'i>,
                         Vec<(Vec<Attribute<'i>>, SimpleIdentifier<'i>, Type<'i>)>,
                         Pair<'i, Rule>),
}

fn pair_to_attrs_and_type<'i>(p: Pair<'i, Rule>) -> (Vec<Attribute<'i>>, Type<'i>) {
    debug_assert!(p.as_rule() == Rule::maybe_attributed_type);

    let mut attrs = vec![];

    for pair in p.into_inner() {
        match pair.as_rule() {
            Rule::attribute => attrs.push(pair_to_attribute(pair)),
            Rule::_type => return (attrs, pair_to_type(pair)),
            _ => unreachable!()
        }
    }

    unreachable!()
}

fn pair_to_attrs_and_named_type_assign<'i>(p: Pair<'i, Rule>) -> (Vec<Attribute<'i>>, SimpleIdentifier<'i>, Type<'i>) {
    debug_assert!(p.as_rule() == Rule::maybe_attributed_named_type_assign);

    let mut attrs = vec![];

    for pair in p.into_inner() {
        match pair.as_rule() {
            Rule::attribute => {
                attrs.push(pair_to_attribute(pair));
            }

            Rule::named_type_assign => {
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

fn pair_to_attrs_and_named_type_annotated<'i>(p: Pair<'i, Rule>) -> (Vec<Attribute<'i>>, SimpleIdentifier<'i>, Type<'i>) {
    debug_assert!(p.as_rule() == Rule::maybe_attributed_named_type_annotated);

    let mut attrs = vec![];

    for pair in p.into_inner() {
        match pair.as_rule() {
            Rule::attribute => {
                attrs.push(pair_to_attribute(pair));
            }

            Rule::named_type_annotated => {
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
    let pair = p.clone().into_inner().next().unwrap();

    match pair.as_rule() {
        Rule::id => return Type::Id(pair_to_identifier(pair), p),

        Rule::type_application_anon => {
            let mut pairs = pair.into_inner();
            let id = pair_to_identifier(pairs.next().unwrap());
            let mut type_args = pairs.map(pair_to_attrs_and_type).collect();
            return Type::TypeApplicationAnon(id, type_args, p);
        }

        Rule::type_application_named => {
            let mut pairs = pair.into_inner();
            let id = pair_to_identifier(pairs.next().unwrap());
            let mut named_type_args = pairs.map(pair_to_attrs_and_named_type_assign).collect();
            return Type::TypeApplicationNamed(id, named_type_args, p);
        }

        Rule::macro_invocation => {
            return Type::MacroInv(pair_to_macro_invocation(pair), p)
        }

        Rule::ptr_type => {
            return Type::Ptr(Box::new(pair_to_type(pair.into_inner().next().unwrap())), p)
        }

        Rule::ptr_mut_type => {
            return Type::PtrMut(Box::new(pair_to_type(pair.into_inner().next().unwrap())), p)
        }

        Rule::array_type => {
            return Type::Array(Box::new(pair_to_type(pair.into_inner().next().unwrap())), p)
        }

        Rule::product_repeated_type => {
            let mut pairs = pair.into_inner();
            let inner = Box::new(pair_to_type(pairs.next().unwrap()));
            let rep = pair_to_repetition(pairs.next().unwrap());
            return Type::ProductRepeated(inner, rep, p);
        }

        Rule::product_anon_type => {
            return Type::ProductAnon(pair.into_inner().map(pair_to_attrs_and_type).collect(), p);
        }

        Rule::product_named_type => {
            return Type::ProductNamed(pair.into_inner().map(pair_to_attrs_and_named_type_annotated).collect(), p);
        }

        Rule::fun_anon_type => {
            let mut pairs = pair.into_inner();
            let mut args = pairs.next().unwrap().into_inner().map(pair_to_attrs_and_type).collect();
            let ret_type = Box::new(pair_to_type(pairs.next().unwrap()));
            return Type::FunAnon(args, ret_type, p);
        }

        Rule::fun_named_type => {
            let mut pairs = pair.into_inner();
            let mut args = pairs.next().unwrap().into_inner().map(pair_to_attrs_and_named_type_annotated).collect();
            let ret_type = Box::new(pair_to_type(pairs.next().unwrap()));
            return Type::FunNamed(args, ret_type, p);
        }

        _ => unreachable!()
    }
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
        &Type::Id(ref id, _) => {
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
        Type::Id(id, _) => {
            assert_eq!(id.0[0].as_str(), "abc");
            assert_eq!(id.0[1].as_str(), "def");
        }
        _ => panic!(),
    }

    match p_type("xyz<abc>").unwrap() {
        Type::TypeApplicationAnon(id, args, _) => {
            assert_sid_id(&id, "xyz");
            assert_sid_type(&args[0].1, "abc");
        }
        _ => panic!(),
    }

    match p_type("xyz<abc, def>").unwrap() {
        Type::TypeApplicationAnon(id, args, _) => {
            assert_sid_id(&id, "xyz");
            assert_sid_type(&args[0].1, "abc");
            assert_sid_type(&args[1].1, "def");
        }
        _ => panic!(),
    }

    match p_type("xyz<abc = def>").unwrap() {
        Type::TypeApplicationNamed(id, triples, _) => {
            assert_sid_id(&id, "xyz");
            assert_eq!(triples[0].0, &[][..]);
            assert_sid(&triples[0].1, "abc");
            assert_sid_type(&triples[0].2, "def");
        }
        _ => panic!(),
    }

    match p_type("xyz<abc = def, ghi = jkl>").unwrap() {
        Type::TypeApplicationNamed(id, triples, _) => {
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
        Type::TypeApplicationAnon(id, args, _) => {
            assert_sid_id(&id, "xyz");
            assert_sid_type(&args[0].1, "abc");
        }
        _ => panic!(),
    }

    match p_type("xyz<#[foo]{abc = def}>").unwrap() {
        Type::TypeApplicationNamed(id, triples, _) => {
            assert_sid_id(&id, "xyz");
            assert_sid_attr(&triples[0].0[0], "foo");
            assert_sid(&triples[0].1, "abc");
            assert_sid_type(&triples[0].2, "def");
        }
        _ => panic!(),
    }

    match p_type("xyz<#[foo]#[bar]{abc = def}>").unwrap() {
        Type::TypeApplicationNamed(id, triples, _) => {
            assert_sid_id(&id, "xyz");
            assert_sid_attr(&triples[0].0[0], "foo");
            assert_sid_attr(&triples[0].0[1], "bar");
            assert_sid(&triples[0].1, "abc");
            assert_sid_type(&triples[0].2, "def");
        }
        _ => panic!(),
    }

    match p_type("$abc()").unwrap() {
        Type::MacroInv(MacroInvocation(id, _, _), _) => {
            assert_eq!(id.0[0].as_str(), "abc");
        }
        _ => panic!(),
    }

    match p_type("$abc::def()").unwrap() {
        Type::MacroInv(MacroInvocation(id, _, _), _) => {
            assert_eq!(id.0[0].as_str(), "abc");
            assert_eq!(id.0[1].as_str(), "def");
        }
        _ => panic!(),
    }

    match p_type("@abc").unwrap() {
        Type::Ptr(inner, _) => {
            assert_sid_type(&inner, "abc");
        }
        _ => panic!(),
    }

    match p_type("~abc").unwrap() {
        Type::PtrMut(inner, _) => {
            assert_sid_type(&inner, "abc");
        }
        _ => panic!(),
    }

    match p_type("[abc]").unwrap() {
        Type::Array(inner, _) => {
            assert_sid_type(&inner, "abc");
        }
        _ => panic!(),
    }

    match p_type("(abc; 42)").unwrap() {
        Type::ProductRepeated(inner, rep, _) => {
            assert_sid_type(&inner, "abc");
            match rep {
                Repetition::Literal(int, _) => assert_eq!(int, 42),
                _ => panic!(),
            }
        }
        _ => panic!(),
    }

    match p_type("()").unwrap() {
        Type::ProductAnon(types, _) => {
            assert_eq!(types, &[][..]);
        }
        _ => panic!(),
    }

    match p_type("(abc)").unwrap() {
        Type::ProductAnon(types, _) => {
            assert_sid_type(&types[0].1, "abc");
        }
        _ => panic!(),
    }

    match p_type("(abc, def)").unwrap() {
        Type::ProductAnon(types, _) => {
            assert_sid_type(&types[0].1, "abc");
            assert_sid_type(&types[1].1, "def");
        }
        _ => panic!(),
    }

    match p_type("(abc: def)").unwrap() {
        Type::ProductNamed(triples, _) => {
            assert_eq!(triples[0].0, &[][..]);
            assert_sid(&triples[0].1, "abc");
            assert_sid_type(&triples[0].2, "def");
        }
        _ => panic!(),
    }

    match p_type("(abc: def, ghi: jkl)").unwrap() {
        Type::ProductNamed(triples, _) => {
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
        Type::ProductNamed(triples, _) => {
            assert_sid_attr(&triples[0].0[0], "foo");
            assert_sid(&triples[0].1, "abc");
            assert_sid_type(&triples[0].2, "def");
        }
        _ => panic!(),
    }

    match p_type("(#[foo]#[bar]{abc: def})").unwrap() {
        Type::ProductNamed(triples, _) => {
            assert_sid_attr(&triples[0].0[0], "foo");
            assert_sid_attr(&triples[0].0[1], "bar");
            assert_sid(&triples[0].1, "abc");
            assert_sid_type(&triples[0].2, "def");
        }
        _ => panic!(),
    }

    match p_type("() -> xyz").unwrap() {
        Type::FunAnon(args, ret, _) => {
            assert_eq!(args, &[][..]);
            assert_sid_type(&ret, "xyz");
        }
        _ => panic!(),
    }

    match p_type("(abc) -> xyz").unwrap() {
        Type::FunAnon(args, ret, _) => {
            assert_sid_type(&args[0].1, "abc");
            assert_sid_type(&ret, "xyz");
        }
        _ => panic!(),
    }

    match p_type("(abc, def) -> xyz").unwrap() {
        Type::FunAnon(args, ret, _) => {
            assert_sid_type(&args[0].1, "abc");
            assert_sid_type(&args[1].1, "def");
            assert_sid_type(&ret, "xyz");
        }
        _ => panic!(),
    }

    match p_type("(abc: def) -> xyz").unwrap() {
        Type::FunNamed(triples, ret, _) => {
            assert_eq!(triples[0].0, &[][..]);
            assert_sid(&triples[0].1, "abc");
            assert_sid_type(&triples[0].2, "def");
            assert_sid_type(&ret, "xyz");
        }
        _ => panic!(),
    }

    match p_type("(abc: def, ghi: jkl) -> xyz").unwrap() {
        Type::FunNamed(triples, ret, _) => {
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
        Type::FunNamed(triples, ret, _) => {
            assert_sid_attr(&triples[0].0[0], "foo");
            assert_sid(&triples[0].1, "abc");
            assert_sid_type(&triples[0].2, "def");
            assert_sid_type(&ret, "xyz");
        }
        _ => panic!(),
    }

    match p_type("(#[foo]#[bar]{abc: def}) -> xyz").unwrap() {
        Type::FunNamed(triples, ret, _) => {
            assert_sid_attr(&triples[0].0[0], "foo");
            assert_sid_attr(&triples[0].0[1], "bar");
            assert_sid(&triples[0].1, "abc");
            assert_sid_type(&triples[0].2, "def");
            assert_sid_type(&ret, "xyz");
        }
        _ => panic!(),
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Summand<'i> {
    Anon(SimpleIdentifier<'i>,  Vec<(Vec<Attribute<'i>>, Type<'i>)>, Pair<'i, Rule>),
    Named(SimpleIdentifier<'i>, Vec<(Vec<Attribute<'i>>, SimpleIdentifier<'i>, Type<'i>)>, Pair<'i, Rule>),
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum TypeDef<'i> {
    Alias(Type<'i>),
    TypeLevelFun(Vec<(Vec<Attribute<'i>>, SimpleIdentifier<'i>)>, Box<TypeDef<'i>>, Pair<'i, Rule>),
    // pub | pub A(Foo, Bar) | pub B | C(x: Foo)
    // Bool is whether the tag constructors are public
    Sum(bool, Vec<(Vec<Attribute<'i>>, Summand<'i>)>, Pair<'i, Rule>),
}

fn pair_to_summand<'i>(p: Pair<'i, Rule>) -> Summand<'i> {
    debug_assert!(p.as_rule() == Rule::summand);

    let mut pairs = p.clone().into_inner();

    let sid = pair_to_simple_identifier(pairs.next().unwrap());

    match pairs.next() {
        None => Summand::Anon(sid, vec![], p),

        Some(pair) => {
            match pair.as_rule() {
                Rule::product_anon_type => {
                    Summand::Anon(sid, pair.into_inner().map(pair_to_attrs_and_type).collect(), p)
                }

                Rule::product_named_type => {
                    Summand::Named(sid, pair.into_inner().map(pair_to_attrs_and_named_type_annotated).collect(), p)
                }

                _ => unreachable!()
            }
        }
    }
}

fn pair_to_attrs_and_summand<'i>(p: Pair<'i, Rule>) -> (Vec<Attribute<'i>>, Summand<'i>) {
    debug_assert!(p.as_rule() == Rule::maybe_attributed_summand);

    let mut attrs = vec![];

    for pair in p.into_inner() {
        match pair.as_rule() {
            Rule::attribute => attrs.push(pair_to_attribute(pair)),
            Rule::summand => return (attrs, pair_to_summand(pair)),
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
            let mut args = vec![];

            for pair in pair.into_inner() {
                match pair.as_rule() {
                    Rule::maybe_attributed_sid => args.push(pair_to_attrs_and_sid(pair)),
                    Rule::type_def => return TypeDef::TypeLevelFun(args, Box::new(pair_to_type_def(pair)), p),
                    _ => unreachable!()
                }
            }
            unreachable!()
        }

        Rule::sum => {
            let mut pairs = pair.into_inner().peekable();

            let public = pairs.peek().unwrap().as_rule() == Rule::_pub;
            if public {
                pairs.next();
            }

            let mut summands = pairs.map(pair_to_attrs_and_summand).collect();

            return TypeDef::Sum(public, summands, p);
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
        TypeDef::Alias(Type::Id(id, _)) => {
            assert_eq!(id.0[0].as_str(), "abc");
            assert_eq!(id.0[1].as_str(), "def");
        }
        _ => panic!()
    }

    match p_type_def("<A> => abc").unwrap() {
        TypeDef::TypeLevelFun(args, ret, _) => {
            assert_eq!(args.len(), 1);
            assert_eq!(args[0].0.len(), 0);
            assert_sid(&args[0].1, "A");
            assert_sid_type_def(ret.as_ref(), "abc");
        }
        _ => panic!()
    }

    match p_type_def("<A, B> => abc").unwrap() {
        TypeDef::TypeLevelFun(args, ret, _) => {
            assert_eq!(args.len(), 2);
            assert_eq!(args[0].0.len(), 0);
            assert_sid(&args[0].1, "A");
            assert_eq!(args[1].0.len(), 0);
            assert_sid(&args[1].1, "B");
            assert_sid_type_def(ret.as_ref(), "abc");
        }
        _ => panic!()
    }

    match p_type_def("<#[foo] { A }> => abc").unwrap() {
        TypeDef::TypeLevelFun(args, ret, _) => {
            assert_eq!(args.len(), 1);
            assert_eq!(args[0].0.len(), 1);
            assert_sid(&args[0].1, "A");
            assert_sid_type_def(ret.as_ref(), "abc");
        }
        _ => panic!()
    }

    match p_type_def("| A").unwrap() {
        TypeDef::Sum(false, summands, _) => {
            assert_eq!(summands.len(), 1);
            assert_eq!(summands[0].0.len(), 0);
            match summands[0].1 {
                Summand::Anon(ref sid, ref fields, _) => {
                    assert_sid(sid, "A");
                    assert_eq!(fields.len(), 0);
                }
                _ => panic!()
            }
        }
        _ => panic!()
    }

    match p_type_def("pub | A").unwrap() {
        TypeDef::Sum(true, summands, _) => {
            assert_eq!(summands.len(), 1);
            assert_eq!(summands[0].0.len(), 0);
            match summands[0].1 {
                Summand::Anon(ref sid, ref fields, _) => {
                    assert_sid(sid, "A");
                    assert_eq!(fields.len(), 0);
                }
                _ => panic!()
            }
        }
        _ => panic!()
    }

    match p_type_def("pub #[foo] { | A }").unwrap() {
        TypeDef::Sum(true, summands, _) => {
            assert_eq!(summands.len(), 1);
            assert_eq!(summands[0].0.len(), 1);
            match summands[0].1 {
                Summand::Anon(ref sid, ref fields, _) => {
                    assert_sid(sid, "A");
                    assert_eq!(fields.len(), 0);
                }
                _ => panic!()
            }
        }
        _ => panic!()
    }

    match p_type_def("| A | B").unwrap() {
        TypeDef::Sum(false, summands, _) => {
            assert_eq!(summands.len(), 2);
            assert_eq!(summands[0].0.len(), 0);
            match summands[0].1 {
                Summand::Anon(ref sid, ref fields, _) => {
                    assert_sid(sid, "A");
                    assert_eq!(fields.len(), 0);
                }
                _ => panic!()
            }
            match summands[1].1 {
                Summand::Anon(ref sid, ref fields, _) => {
                    assert_sid(sid, "B");
                    assert_eq!(fields.len(), 0);
                }
                _ => panic!()
            }
        }
        _ => panic!()
    }

    match p_type_def("| A(B)").unwrap() {
        TypeDef::Sum(false, summands, _) => {
            assert_eq!(summands.len(), 1);
            assert_eq!(summands[0].0.len(), 0);
            match summands[0].1 {
                Summand::Anon(ref sid, ref fields, _) => {
                    assert_sid(sid, "A");
                    assert_eq!(fields.len(), 1);
                    assert_sid_type(&fields[0].1, "B");
                }
                _ => panic!()
            }
        }
        _ => panic!()
    }

    match p_type_def("| A(b: C)").unwrap() {
        TypeDef::Sum(false, summands, _) => {
            assert_eq!(summands.len(), 1);
            assert_eq!(summands[0].0.len(), 0);
            match summands[0].1 {
                Summand::Named(ref sid, ref fields, _) => {
                    assert_sid(sid, "A");
                    assert_eq!(fields.len(), 1);
                }
                _ => panic!()
            }
        }
        _ => panic!()
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Pattern<'i> {
    Blank(Pair<'i, Rule>),
    Id(bool, SimpleIdentifier<'i>, Option<Type<'i>>, Pair<'i, Rule>),
    Literal(Literal<'i>),
    Ptr(Box<Pattern<'i>>, Pair<'i, Rule>),
    ProductAnon(Vec<(Vec<Attribute<'i>>, Pattern<'i>)>, Pair<'i, Rule>),
    ProductNamed(Vec<(Vec<Attribute<'i>>, SimpleIdentifier<'i>, Pattern<'i>)>, Pair<'i, Rule>),
    SummandAnon(SimpleIdentifier<'i>, Vec<(Vec<Attribute<'i>>, Pattern<'i>)>, Pair<'i, Rule>),
    SummandNamed(SimpleIdentifier<'i>, Vec<(Vec<Attribute<'i>>, SimpleIdentifier<'i>, Pattern<'i>)>, Pair<'i, Rule>)
}

impl<'i> Pattern<'i> {
    pub fn pair(&self) -> &Pair<'i, Rule> {
        match self {
            &Pattern::Blank(ref pair) => pair,
            &Pattern::Id(_, _, _, ref pair) => pair,
            &Pattern::Literal(ref lit) => lit.pair(),
            &Pattern::Ptr(_, ref pair) => pair,
            &Pattern::ProductAnon(_, ref pair) => pair,
            &Pattern::ProductNamed(_, ref pair) => pair,
            &Pattern::SummandAnon(_, _, ref pair) => pair,
            &Pattern::SummandNamed(_, _, ref pair) => pair,
        }
    }
}

fn pair_to_attrs_and_named_pattern_assign<'i>(p: Pair<'i, Rule>) -> (Vec<Attribute<'i>>, SimpleIdentifier<'i>, Pattern<'i>) {
    debug_assert!(p.as_rule() == Rule::maybe_attributed_named_pattern_assign);

    let mut attrs = vec![];

    for pair in p.into_inner() {
        match pair.as_rule() {
            Rule::attribute => {
                attrs.push(pair_to_attribute(pair));
            }

            Rule::named_pattern_assign => {
                let mut pairs = pair.into_inner();
                let sid = pair_to_simple_identifier(pairs.next().unwrap());
                let pattern = pair_to_pattern(pairs.next().unwrap());
                return (attrs, sid, pattern)
            }

            _ => unreachable!()
        }
    }

    unreachable!()
}

fn pair_to_attrs_and_pattern<'i>(p: Pair<'i, Rule>) -> (Vec<Attribute<'i>>, Pattern<'i>) {
    debug_assert!(p.as_rule() == Rule::maybe_attributed_pattern);

    let mut attrs = vec![];

    for pair in p.into_inner() {
        match pair.as_rule() {
            Rule::attribute => attrs.push(pair_to_attribute(pair)),
            Rule::pattern => return (attrs, pair_to_pattern(pair)),
            _ => unreachable!(),
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
            Pattern::ProductAnon(pair.into_inner().map(pair_to_attrs_and_pattern).collect(), p)
        }

        Rule::product_named_pattern => {
            Pattern::ProductNamed(pair.into_inner().map(pair_to_attrs_and_named_pattern_assign).collect(), p)
        }

        Rule::summand_pattern => {
            let mut pairs = pair.into_inner();
            let sid = pair_to_simple_identifier(pairs.next().unwrap());

            match pairs.next() {
                None => Pattern::SummandAnon(sid, vec![], p),

                Some(pair) => {
                    match pair.as_rule() {
                        Rule::product_anon_pattern => {
                            Pattern::SummandAnon(sid, pair.into_inner().map(pair_to_attrs_and_pattern).collect(), p)
                        }

                        Rule::product_named_pattern => {
                            Pattern::SummandNamed(sid, pair.into_inner().map(pair_to_attrs_and_named_pattern_assign).collect(), p)
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
        Pattern::SummandAnon(sid, inner, _) => {
            assert_sid(&sid, "abc");
            assert_eq!(inner.len(), 0);
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

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum PatternIrref<'i> {
    Blank(Pair<'i, Rule>),
    Id(bool, SimpleIdentifier<'i>, Option<Type<'i>>, Pair<'i, Rule>),
    Ptr(Box<PatternIrref<'i>>, Pair<'i, Rule>),
    ProductAnon(Vec<(Vec<Attribute<'i>>, PatternIrref<'i>)>, Pair<'i, Rule>),
    ProductNamed(Vec<(Vec<Attribute<'i>>, SimpleIdentifier<'i>, PatternIrref<'i>)>, Pair<'i, Rule>),
}

impl<'i> PatternIrref<'i> {
    pub fn pair(&self) -> &Pair<'i, Rule> {
        match self {
            &PatternIrref::Blank(ref pair) => pair,
            &PatternIrref::Id(_, _, _, ref pair) => pair,
            &PatternIrref::Ptr(_, ref pair) => pair,
            &PatternIrref::ProductAnon(_, ref pair) => pair,
            &PatternIrref::ProductNamed(_, ref pair) => pair,
        }
    }
}

fn pair_to_attrs_and_named_pattern_irref_assign<'i>(p: Pair<'i, Rule>) -> (Vec<Attribute<'i>>, SimpleIdentifier<'i>, PatternIrref<'i>) {
    debug_assert!(p.as_rule() == Rule::maybe_attributed_named_pattern_irref_assign);

    let mut attrs = vec![];

    for pair in p.into_inner() {
        match pair.as_rule() {
            Rule::attribute => {
                attrs.push(pair_to_attribute(pair));
            }

            Rule::named_pattern_irref_assign => {
                let mut pairs = pair.into_inner();
                let sid = pair_to_simple_identifier(pairs.next().unwrap());
                let pattern = pair_to_pattern_irref(pairs.next().unwrap());
                return (attrs, sid, pattern)
            }

            _ => unreachable!()
        }
    }

    unreachable!()
}

fn pair_to_attrs_and_pattern_irref<'i>(p: Pair<'i, Rule>) -> (Vec<Attribute<'i>>, PatternIrref<'i>) {
    debug_assert!(p.as_rule() == Rule::maybe_attributed_pattern_irref);

    let mut attrs = vec![];

    for pair in p.into_inner() {
        match pair.as_rule() {
            Rule::attribute => attrs.push(pair_to_attribute(pair)),
            Rule::pattern_irref => return (attrs, pair_to_pattern_irref(pair)),
            _ => unreachable!(),
        }
    }
    unreachable!()
}

fn pair_to_pattern_irref<'i>(p: Pair<'i, Rule>) -> PatternIrref<'i> {
    debug_assert!(p.as_rule() == Rule::pattern_irref);
    let pair = p.clone().into_inner().next().unwrap();

    match pair.as_rule() {
        Rule::blank_pattern => {
            PatternIrref::Blank(p)
        }

        Rule::ptr_pattern_irref => {
            PatternIrref::Ptr(Box::new(pair_to_pattern_irref(pair.into_inner().next().unwrap())), p)
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

            PatternIrref::Id(mutable, sid, type_annotation, p)
        }

        Rule::product_anon_pattern_irref => {
            PatternIrref::ProductAnon(pair.into_inner().map(pair_to_attrs_and_pattern_irref).collect(), p)
        }

        Rule::product_named_pattern_irref => {
            PatternIrref::ProductNamed(pair.into_inner().map(pair_to_attrs_and_named_pattern_irref_assign).collect(), p)
        }

        _ => unreachable!()
    }
}

pub fn p_pattern_irref<'i>(input: &'i str) -> PestResult<PatternIrref<'i>> {
    LookParser::parse(Rule::pattern_irref, input).map(|mut pairs| pair_to_pattern_irref(pairs.next().unwrap()))
}

#[test]
fn test_pattern_irref() {
    match p_pattern_irref("_").unwrap() {
        PatternIrref::Blank(_) => {}
        _ => panic!()
    }

    match p_pattern_irref("_abc").unwrap() {
        PatternIrref::Id(mutable, sid, type_annotation, _) => {
            assert!(!mutable);
            assert_sid(&sid, "_abc");
            assert_eq!(type_annotation, None);
        }
        _ => panic!()
    }

    match p_pattern_irref("mut abc").unwrap() {
        PatternIrref::Id(mutable, sid, type_annotation, _) => {
            assert!(mutable);
            assert_sid(&sid, "abc");
            assert_eq!(type_annotation, None);
        }
        _ => panic!()
    }

    match p_pattern_irref("abc: T").unwrap() {
        PatternIrref::Id(mutable, sid, type_annotation, _) => {
            assert!(!mutable);
            assert_sid(&sid, "abc");
            assert_sid_type(&type_annotation.unwrap(), "T");
        }
        _ => panic!()
    }

    match p_pattern_irref("@_").unwrap() {
        PatternIrref::Ptr(inner, _) => {
            match inner.as_ref() {
                &PatternIrref::Blank(_) => {},
                _ => panic!()
            }
        }
        _ => panic!()
    }

    match p_pattern_irref("()").unwrap() {
        PatternIrref::ProductAnon(inner, _) => {
            assert_eq!(inner.len(), 0);
        }
        _ => panic!()
    }

    match p_pattern_irref("(_)").unwrap() {
        PatternIrref::ProductAnon(inner, _) => {
            assert_eq!(inner.len(), 1);
            assert_eq!(inner[0].0.len(), 0);
        }
        _ => panic!()
    }

    match p_pattern_irref("(_, _)").unwrap() {
        PatternIrref::ProductAnon(inner, _) => {
            assert_eq!(inner.len(), 2);
            assert_eq!(inner[0].0.len(), 0);
            assert_eq!(inner[1].0.len(), 0);
        }
        _ => panic!()
    }

    match p_pattern_irref("(#[foo] { _ } )").unwrap() {
        PatternIrref::ProductAnon(inner, _) => {
            assert_eq!(inner.len(), 1);
            assert_eq!(inner[0].0.len(), 1);
        }
        _ => panic!()
    }

    match p_pattern_irref("(#[foo] #[bar] { _ } )").unwrap() {
        PatternIrref::ProductAnon(inner, _) => {
            assert_eq!(inner.len(), 1);
            assert_eq!(inner[0].0.len(), 2);
        }
        _ => panic!()
    }

    match p_pattern_irref("(abc = _)").unwrap() {
        PatternIrref::ProductNamed(inner, _) => {
            assert_eq!(inner.len(), 1);
            assert_eq!(inner[0].0.len(), 0);
            assert_sid(&inner[0].1, "abc");
        }
        _ => panic!()
    }

    match p_pattern_irref("(abc = _, def = _)").unwrap() {
        PatternIrref::ProductNamed(inner, _) => {
            assert_eq!(inner.len(), 2);
            assert_eq!(inner[0].0.len(), 0);
            assert_sid(&inner[0].1, "abc");
            assert_eq!(inner[1].0.len(), 0);
            assert_sid(&inner[1].1, "def");
        }
        _ => panic!()
    }

    match p_pattern_irref("(#[foo] { abc = _ } )").unwrap() {
        PatternIrref::ProductNamed(inner, _) => {
            assert_eq!(inner.len(), 1);
            assert_eq!(inner[0].0.len(), 1);
            assert_sid(&inner[0].1, "abc");
        }
        _ => panic!()
    }

    match p_pattern_irref("(#[foo] #[bar] { abc = _ } )").unwrap() {
        PatternIrref::ProductNamed(inner, _) => {
            assert_eq!(inner.len(), 1);
            assert_eq!(inner[0].0.len(), 2);
            assert_sid(&inner[0].1, "abc");
        }
        _ => panic!()
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct AnnotatedBinding<'i>(bool, SimpleIdentifier<'i>, Type<'i>);

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct FunLiteral<'i>(Vec<(Vec<Attribute<'i>>, AnnotatedBinding<'i>)>, Type<'i>, Vec<(Vec<Attribute<'i>>, Expression<'i>)>);

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum LValue<'i> {
    Id(Identifier<'i>, Pair<'i, Rule>),
    DerefMut(Box<LValue<'i>>, Pair<'i, Rule>),
    ArrayIndex(Box<LValue<'i>>, Box<Expression<'i>>, Pair<'i, Rule>),
    ProductAccessAnon(Box<LValue<'i>>, u64, Pair<'i, Rule>),
    ProductAccessNamed(Box<LValue<'i>>, SimpleIdentifier<'i>, Pair<'i, Rule>),
}

fn pair_to_lvalue<'i>(p: Pair<'i, Rule>) -> LValue<'i> {
    debug_assert!(p.as_rule() == Rule::lvalue);

    let mut pairs = p.clone().into_inner();

    let mut lval = LValue::Id(pair_to_identifier(pairs.next().unwrap()), p.clone());

    let pair_lvalue_ = pairs.next().unwrap();
    debug_assert!(pair_lvalue_.as_rule() == Rule::lvalue_);

    for pair in pair_lvalue_.into_inner() {
        match pair.as_rule() {
            Rule::deref_mut_ => lval = LValue::DerefMut(Box::new(lval), p.clone()),
            Rule::array_index_ => {
                lval = LValue::ArrayIndex(
                    Box::new(lval),
                    Box::new(pair_to_expression(pair.into_inner().next().unwrap())),
                    p.clone()
                );
            }
            Rule::product_access_named_ => {
                lval = LValue::ProductAccessNamed(
                    Box::new(lval),
                    pair_to_simple_identifier(pair.into_inner().next().unwrap()),
                    p.clone()
                );
            }
            Rule::product_access_anon_ => {
                let mut digits: Vec<u8> = vec![];
                digits.extend(pair.into_inner().next().unwrap().as_str().as_bytes());
                digits.retain(|byte| *byte != 95);
                let int = u64::from_str_radix(unsafe {
                                              &String::from_utf8_unchecked(digits)
                                          }, 10).unwrap();

                lval = LValue::ProductAccessAnon(Box::new(lval), int, p.clone());
            }
            _ => unreachable!(),
        }
    }

    lval
}

pub fn p_lvalue<'i>(input: &'i str) -> PestResult<LValue<'i>> {
    LookParser::parse(Rule::lvalue, input).map(|mut pairs| pair_to_lvalue(pairs.next().unwrap()))
}

#[cfg(test)]
fn assert_sid_lvalue(t: &LValue, expected: &str) {
    match t {
        &LValue::Id(ref id, _) => {
            assert_eq!(id.0[0].as_str(), expected);
        }
        _ => panic!(),
    }
}

#[test]
fn test_lvalue() {
    assert_sid_lvalue(&p_lvalue("abc").unwrap(), "abc");

    match p_lvalue("abc~").unwrap() {
        LValue::DerefMut(inner, _) => {
            assert_sid_lvalue(inner.as_ref(), "abc");
        }
        _ => panic!()
    }

    match p_lvalue("abc~~").unwrap() {
        LValue::DerefMut(inner, _) => {
            match inner.as_ref() {
                &LValue::DerefMut(ref inner, _) => {
                    assert_sid_lvalue(inner.as_ref(), "abc");
                }
                _ => panic!()
            }
        }
        _ => panic!()
    }

    match p_lvalue("abc[def]").unwrap() {
        LValue::ArrayIndex(inner, index, _) => {
            assert_sid_lvalue(inner.as_ref(), "abc");
            assert_sid_expression(index.as_ref(), "def");
        }
        _ => panic!()
    }

    match p_lvalue("abc.0").unwrap() {
        LValue::ProductAccessAnon(inner, 0, _) => {
            assert_sid_lvalue(inner.as_ref(), "abc");
        }
        _ => panic!()
    }

    match p_lvalue("abc.def").unwrap() {
        LValue::ProductAccessNamed(inner, field, _) => {
            assert_sid_lvalue(inner.as_ref(), "abc");
            assert_sid(&field, "def");
        }
        _ => panic!()
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Expression<'i> {
    Id(Identifier<'i>, Pair<'i, Rule>),
    Literal(Literal<'i>, Pair<'i, Rule>),
    MacroInv(MacroInvocation<'i>, Pair<'i, Rule>),
    Ref(Box<Expression<'i>>, Pair<'i, Rule>),
    RefMut(Box<Expression<'i>>, Pair<'i, Rule>),
    Deref(Box<Expression<'i>>, Pair<'i, Rule>),
    DerefMut(Box<Expression<'i>>, Pair<'i, Rule>),
    Array(Box<Expression<'i>>, Pair<'i, Rule>),
    ArrayIndex(Box<Expression<'i>>, Box<Expression<'i>>, Pair<'i, Rule>),
    ProductRepeated(Box<Expression<'i>>, Repetition<'i>, Pair<'i, Rule>),
    ProductAnon(Vec<(Vec<Attribute<'i>>, Expression<'i>)>, Pair<'i, Rule>),
    ProductNamed(Vec<(Vec<Attribute<'i>>, SimpleIdentifier<'i>, Expression<'i>)>, Pair<'i, Rule>),
    ProductAccessAnon(Box<Expression<'i>>, u64, Pair<'i, Rule>),
    ProductAccessNamed(Box<Expression<'i>>, SimpleIdentifier<'i>, Pair<'i, Rule>),
    FunLiteral(FunLiteral<'i>, Pair<'i, Rule>),
    FunApplicationAnon(Box<Expression<'i>>, Vec<(Vec<Attribute<'i>>, Expression<'i>)>, Pair<'i, Rule>),
    FunApplicationNamed(Box<Expression<'i>>, Vec<(Vec<Attribute<'i>>, SimpleIdentifier<'i>, Expression<'i>)>, Pair<'i, Rule>),
    Generic(Vec<(Vec<Attribute<'i>>, SimpleIdentifier<'i>)>, Box<Expression<'i>>, Pair<'i, Rule>),
    TypeApplicationAnon(Identifier<'i>, Vec<(Vec<Attribute<'i>>, Type<'i>)>, Pair<'i, Rule>),
    TypeApplicationNamed(Identifier<'i>,
                         Vec<(Vec<Attribute<'i>>, SimpleIdentifier<'i>, Type<'i>)>,
                         Pair<'i, Rule>),
    Cast(Box<Expression<'i>>, Type<'i>, Pair<'i, Rule>),
    LAnd(Box<Expression<'i>>, Box<Expression<'i>>, Pair<'i, Rule>),
    LOr(Box<Expression<'i>>, Box<Expression<'i>>, Pair<'i, Rule>),
    Assignment(LValue<'i>, Box<Expression<'i>>, Pair<'i, Rule>),
    Val(PatternIrref<'i>, Option<Box<Expression<'i>>>, Pair<'i, Rule>),
    If(Box<Expression<'i>>, Vec<(Vec<Attribute<'i>>, Expression<'i>)>, Option<Vec<(Vec<Attribute<'i>>, Expression<'i>)>>, Pair<'i, Rule>),
    Case(Box<Expression<'i>>, Vec<(Vec<Attribute<'i>>, Pattern<'i>, Vec<(Vec<Attribute<'i>>, Expression<'i>)>)>, Pair<'i, Rule>),
    While(Box<Expression<'i>>, Vec<(Vec<Attribute<'i>>, Expression<'i>)>, Pair<'i, Rule>),
    Loop(Box<Expression<'i>>, Vec<(Vec<Attribute<'i>>, Pattern<'i>, Vec<(Vec<Attribute<'i>>, Expression<'i>)>)>, Pair<'i, Rule>),
    Return(Option<Box<Expression<'i>>>, Pair<'i, Rule>),
    Break(Option<Box<Expression<'i>>>, Pair<'i, Rule>),
    Block(Vec<(Vec<Attribute<'i>>, Expression<'i>)>, Pair<'i, Rule>),
}

impl<'i> Expression<'i> {
//     pub fn pair(&self) -> &Pair<'i, Rule> {
//         match self {
//             &Expression::Id(_, _, ref pair) => pair,
//             &Expression::Literal(_ , _, ref pair) => pair,
//             &Expression::MacroInv(_, _, ref pair) => pair,
//             &Expression::Ref(_, _, ref pair) => pair,
//             &Expression::RefMut(_, _, ref pair) => pair,
//             &Expression::Deref(_, _, ref pair) => pair,
//             &Expression::DerefMut(_, _, ref pair) => pair,
//             &Expression::Array(_, _, ref pair) => pair,
//             &Expression::ArrayIndex(_, _, _, ref pair) => pair,
//             &Expression::ProductRepeated(_, _, _, ref pair) => pair,
//             &Expression::ProductAnon(_, _,ref pair) => pair,
//             &Expression::ProductNamed(_, _, ref pair) => pair,
//             &Expression::ProductAccessAnon(_, _, _, ref pair) => pair,
//             &Expression::ProductAccessNamed(_, _, _, ref pair) => pair,
//             &Expression::FunLiteral(_, _, _, _, ref pair) => pair,
//             &Expression::FunApplicationAnon(_, _, _, ref pair) => pair,
//             &Expression::FunApplicationNamed(_, _, _, ref pair) => pair,
//             &Expression::Generic(_, _, _, ref pair) => pair,
//             &Expression::TypeApplicationAnon(_, _, _, ref pair) => pair,
//             &Expression::TypeApplicationNamed(_, _, _, ref pair) => pair,
//             &Expression::Cast(_, _, _, ref pair) => pair,
//             &Expression::LAnd(_, _, _, ref pair) => pair,
//             &Expression::LOr(_, _, _, ref pair) => pair,
//             &Expression::Assignment(_, _, _, ref pair) => pair,
//             &Expression::Val(_, _, _, ref pair) => pair,
//             &Expression::If(_, _, _, _, ref pair) => pair,
//             &Expression::Case(_, _, _, ref pair) => pair,
//             &Expression::While(_, _, _, ref pair) => pair,
//             &Expression::Loop(_, _, _, ref pair) => pair,
//             &Expression::Return(_, _, ref pair) => pair,
//             &Expression::Break(_, _, ref pair) => pair,
//         }
//     }
}

fn pair_to_attrs_and_patterned_block<'i>(p: Pair<'i, Rule>) -> (Vec<Attribute<'i>>, Pattern<'i>, Vec<(Vec<Attribute<'i>>, Expression<'i>)>) {
    debug_assert!(p.as_rule() == Rule::maybe_attributed_patterned_block);

    let mut attrs = vec![];

    for pair in p.into_inner() {
        match pair.as_rule() {
            Rule::attribute => {
                attrs.push(pair_to_attribute(pair));
            }

            Rule::patterned_block => {
                let mut pairs = pair.into_inner();
                let pattern = pair_to_pattern(pairs.next().unwrap());
                let block = pair_to_block(pairs.next().unwrap());
                return (attrs, pattern, block)
            }

            _ => unreachable!()
        }
    }

    unreachable!()
}

fn pair_to_attrs_and_expression<'i>(p: Pair<'i, Rule>) -> (Vec<Attribute<'i>>, Expression<'i>) {
    debug_assert!(p.as_rule() == Rule::maybe_attributed_expression);

    let mut attrs = vec![];

    for pair in p.into_inner() {
        match pair.as_rule() {
            Rule::attribute => attrs.push(pair_to_attribute(pair)),
            Rule::expression => return (attrs, pair_to_expression(pair)),
            _ => unreachable!()
        }
    }

    unreachable!()
}

fn pair_to_attrs_and_named_expression_assign<'i>(p: Pair<'i, Rule>) -> (Vec<Attribute<'i>>, SimpleIdentifier<'i>, Expression<'i>) {
    debug_assert!(p.as_rule() == Rule::maybe_attributed_named_expression_assign);

    let mut attrs = vec![];

    for pair in p.into_inner() {
        match pair.as_rule() {
            Rule::attribute => {
                attrs.push(pair_to_attribute(pair));
            }

            Rule::named_expression_assign => {
                let mut pairs = pair.into_inner();
                let sid = pair_to_simple_identifier(pairs.next().unwrap());
                let _type = pair_to_expression(pairs.next().unwrap());
                return (attrs, sid, _type)
            }

            _ => unreachable!()
        }
    }

    unreachable!()
}

fn pair_to_block<'i>(p: Pair<'i, Rule>) -> Vec<(Vec<Attribute<'i>>, Expression<'i>)> {
    debug_assert!(p.as_rule() == Rule::block);
    p.into_inner().map(pair_to_attrs_and_expression).collect()
}

fn pair_to_annotated_id_pattern<'i>(p: Pair<'i, Rule>) -> AnnotatedBinding<'i> {
    debug_assert!(p.as_rule() == Rule::annotated_id_pattern);
    let mut pairs = p.clone().into_inner().peekable();

    let mutable = pairs.peek().unwrap().as_rule() == Rule::_mut;
    if mutable {
        pairs.next();
    }
    let sid = pair_to_simple_identifier(pairs.next().unwrap());
    let annotation = pair_to_type(pairs.next().unwrap());

    AnnotatedBinding(mutable, sid, annotation)
}

fn pair_to_attrs_and_annotated_binding<'i>(p: Pair<'i, Rule>) -> (Vec<Attribute<'i>>, AnnotatedBinding<'i>) {
    debug_assert!(p.as_rule() == Rule::maybe_attributed_annotated_id_pattern);

    let mut attrs = vec![];

    for pair in p.into_inner() {
        match pair.as_rule() {
            Rule::attribute => attrs.push(pair_to_attribute(pair)),
            Rule::annotated_id_pattern => return (attrs, pair_to_annotated_id_pattern(pair)),
            _ => unreachable!()
        }
    }

    unreachable!()
}

fn pair_to_fun_args<'i>(p: Pair<'i, Rule>) -> Vec<(Vec<Attribute<'i>>, AnnotatedBinding<'i>)> {
    debug_assert!(p.as_rule() == Rule::fun_args);
    p.into_inner().map(pair_to_attrs_and_annotated_binding).collect()
}

fn pair_to_if_expression<'i>(p: Pair<'i, Rule>) -> Expression<'i> {
    debug_assert!(p.as_rule() == Rule::if_expression);

    let mut pairs = p.clone().into_inner();
    assert_eq!(pairs.next().unwrap().as_rule(), Rule::_if);
    let cond = pair_to_expression(pairs.next().unwrap());
    let if_block = pair_to_block(pairs.next().unwrap());

    match pairs.next() {
        Some(pair) => {
            assert_eq!(pair.as_rule(), Rule::_else);

            let pair = pairs.next().unwrap();
            match pair.as_rule() {
                Rule::if_expression => {
                    return Expression::If(
                        Box::new(cond),
                        if_block,
                        Some(vec![(vec![], pair_to_if_expression(pair))]),
                        p
                    );
                }
                Rule::block => {
                    return Expression::If(Box::new(cond), if_block, Some(pair_to_block(pair)), p);
                }
                _ => unreachable!()
            }
        }
        None => return Expression::If(Box::new(cond), if_block, None, p)
    }
}

fn pair_to_expression<'i>(p: Pair<'i, Rule>) -> Expression<'i> {
    debug_assert!(p.as_rule() == Rule::expression);

    let mut pairs = p.clone().into_inner();
    let pair_lexp = pairs.next().unwrap();
    debug_assert!(pair_lexp.as_rule() == Rule::lexpression);
    let pair_exp_ = pairs.next().unwrap();
    debug_assert!(pair_exp_.as_rule() == Rule::expression_);

    let pair = pair_lexp.into_inner().next().unwrap();
    let mut exp = match pair.as_rule() {
        Rule::id => Expression::Id(pair_to_identifier(pair), p.clone()),
        Rule::literal => Expression::Literal(pair_to_literal(pair), p.clone()),
        Rule::macro_invocation => Expression::MacroInv(pair_to_macro_invocation(pair), p.clone()),
        Rule::block => Expression::Block(pair_to_block(pair), p.clone()),
        Rule::ref_expression => {
            Expression::Ref(Box::new(pair_to_expression(pair.into_inner().next().unwrap())), p.clone())
        }
        Rule::ref_mut_expression => {
            Expression::RefMut(Box::new(pair_to_expression(pair.into_inner().next().unwrap())), p.clone())
        }
        Rule::array_expression => {
            Expression::Array(Box::new(pair_to_expression(pair.into_inner().next().unwrap())), p.clone())
        }
        Rule::product_repeated_expression => {
            let mut pairs = pair.into_inner();
            Expression::ProductRepeated(
                Box::new(pair_to_expression(pairs.next().unwrap())),
                pair_to_repetition(pairs.next().unwrap()),
                p.clone()
            )
        }
        Rule::product_anon_expression => {
            Expression::ProductAnon(pair.into_inner().map(pair_to_attrs_and_expression).collect(), p.clone())
        }
        Rule::product_named_expression => {
            Expression::ProductNamed(
                pair.into_inner().map(pair_to_attrs_and_named_expression_assign).collect(),
                p.clone()
            )
        }
        Rule::fun_literal => {
            let mut pairs = pair.into_inner();
            let args = pair_to_fun_args(pairs.next().unwrap());
            let ret_type = pair_to_type(pairs.next().unwrap());
            let body = pair_to_block(pairs.next().unwrap());
            Expression::FunLiteral(FunLiteral(args, ret_type, body), p.clone())
        }
        Rule::generic_expression => {
            let mut pairs = pair.into_inner();
            let args = pairs.next().unwrap().into_inner().map(pair_to_attrs_and_sid).collect();
            let inner_exp = pair_to_expression(pairs.next().unwrap());
            Expression::Generic(args, Box::new(inner_exp), p.clone())
        }
        Rule::type_application_anon => {
            let mut pairs = pair.into_inner();
            let id = pair_to_identifier(pairs.next().unwrap());
            let args = pairs.map(pair_to_attrs_and_type).collect();
            Expression::TypeApplicationAnon(id, args, p.clone())
        }
        Rule::type_application_named => {
            let mut pairs = pair.into_inner();
            let id = pair_to_identifier(pairs.next().unwrap());
            let named_type_args = pairs.map(pair_to_attrs_and_named_type_assign).collect();
            Expression::TypeApplicationNamed(id, named_type_args, p.clone())
        }
        Rule::assignment_expression => {
            let mut pairs = pair.into_inner();
            let lval = pair_to_lvalue(pairs.next().unwrap());
            let exp = pair_to_expression(pairs.next().unwrap());
            Expression::Assignment(lval, Box::new(exp), p.clone())
        }
        Rule::val_expression => {
            let mut pairs = pair.into_inner();
            debug_assert!(pairs.next().unwrap().as_rule() == Rule::_val);
            let pattern = pair_to_pattern_irref(pairs.next().unwrap());

            match pairs.next() {
                Some(pair) => {
                    Expression::Val(pattern, Some(Box::new(pair_to_expression(pair))), p.clone())
                }
                None => {
                    Expression::Val(pattern, None, p.clone())
                }
            }
        }
        Rule::if_expression => {
            pair_to_if_expression(pair)
        }
        Rule::case_expression => {
            let mut pairs = pair.into_inner();
            debug_assert!(pairs.next().unwrap().as_rule() == Rule::_case);

            let matcher = pair_to_expression(pairs.next().unwrap());
            let branches = pairs.map(pair_to_attrs_and_patterned_block).collect();
            Expression::Case(Box::new(matcher), branches, p.clone())
        }
        Rule::while_expression => {
            let mut pairs = pair.into_inner();
            debug_assert!(pairs.next().unwrap().as_rule() == Rule::_while);
            let cond = pair_to_expression(pairs.next().unwrap());
            let block = pair_to_block(pairs.next().unwrap());

            Expression::While(Box::new(cond), block, p.clone())
        }
        Rule::loop_expression => {
            let mut pairs = pair.into_inner();
            debug_assert!(pairs.next().unwrap().as_rule() == Rule::_loop);

            let matcher = pair_to_expression(pairs.next().unwrap());
            let branches = pairs.map(pair_to_attrs_and_patterned_block).collect();
            Expression::Loop(Box::new(matcher), branches, p.clone())
        }
        Rule::return_expression => {
            let mut pairs = pair.into_inner();
            debug_assert!(pairs.next().unwrap().as_rule() == Rule::_return);

            match pairs.next() {
                Some(pair) => {
                    Expression::Return(Some(Box::new(pair_to_expression(pair))), p.clone())
                }
                None => {
                    Expression::Return(None, p.clone())
                }
            }
        }

        Rule::break_expression => {
            let mut pairs = pair.into_inner();
            debug_assert!(pairs.next().unwrap().as_rule() == Rule::_break);

            match pairs.next() {
                Some(pair) => {
                    Expression::Break(Some(Box::new(pair_to_expression(pair))), p.clone())
                }
                None => {
                    Expression::Break(None, p.clone())
                }
            }
        }
        _ => unreachable!()
    };

    for pair in pair_exp_.into_inner() {
        match pair.as_rule() {
            Rule::deref_ => exp = Expression::Deref(Box::new(exp), p.clone()),
            Rule::deref_mut_ => exp = Expression::DerefMut(Box::new(exp), p.clone()),
            Rule::array_index_ => {
                exp = Expression::ArrayIndex(
                    Box::new(exp),
                    Box::new(pair_to_expression(pair.into_inner().next().unwrap())),
                    p.clone()
                );
            }
            Rule::product_access_named_ => {
                exp = Expression::ProductAccessNamed(
                    Box::new(exp),
                    pair_to_simple_identifier(pair.into_inner().next().unwrap()),
                    p.clone()
                );
            }
            Rule::product_access_anon_ => {
                let mut digits: Vec<u8> = vec![];
                digits.extend(pair.into_inner().next().unwrap().as_str().as_bytes());
                digits.retain(|byte| *byte != 95);
                let int = u64::from_str_radix(unsafe {
                                              &String::from_utf8_unchecked(digits)
                                          }, 10).unwrap();

                exp = Expression::ProductAccessAnon(Box::new(exp), int, p.clone());
            }
            Rule::product_anon_expression => {
                exp = Expression::FunApplicationAnon(
                    Box::new(exp),
                    pair.into_inner().map(pair_to_attrs_and_expression).collect(),
                    p.clone()
                );
            }
            Rule::product_named_expression => {
                exp = Expression::FunApplicationNamed(
                    Box::new(exp),
                    pair.into_inner().map(pair_to_attrs_and_named_expression_assign).collect(),
                    p.clone()
                );
            }
            Rule::cast_ => {
                let mut pairs = pair.into_inner();
                assert_eq!(pairs.next().unwrap().as_rule(), Rule::_as);
                exp = Expression::Cast(
                    Box::new(exp),
                    pair_to_type(pairs.next().unwrap()),
                    p.clone()
                );
            }
            Rule::land_ => {
                exp = Expression::LAnd(
                    Box::new(exp),
                    Box::new(pair_to_expression(pair.into_inner().next().unwrap())),
                    p.clone()
                );
            }
            Rule::lor_ => {
                exp = Expression::LOr(
                    Box::new(exp),
                    Box::new(pair_to_expression(pair.into_inner().next().unwrap())),
                    p.clone()
                );
            }
            _ => unreachable!(),
        }
    }

    exp
}

pub fn p_expression<'i>(input: &'i str) -> PestResult<Expression<'i>> {
    LookParser::parse(Rule::expression, input).map(|mut pairs| pair_to_expression(pairs.next().unwrap()))
}

#[cfg(test)]
fn assert_sid_expression(t: &Expression, expected: &str) {
    match t {
        &Expression::Id(ref id, _) => {
            assert_eq!(id.0[0].as_str(), expected);
        }
        _ => panic!(),
    }
}

#[test]
fn test_expression() {
    assert_sid_expression(&p_expression("abc").unwrap(), "abc");

    match p_expression("42").unwrap() {
        Expression::Literal(Literal::Int(int, _), _) => assert_eq!(int, 42),
        _ => panic!()
    }

    match p_expression("12.34").unwrap() {
        Expression::Literal(Literal::Float(float, _), _) => assert_eq!(float, 12.34),
        _ => panic!()
    }

    match p_expression("\"\"").unwrap() {
        Expression::Literal(Literal::String(string, _), _) => assert_eq!(string, ""),
        _ => panic!()
    }

    match p_expression("$abc()").unwrap() {
        Expression::MacroInv(MacroInvocation(id, _, _), _) => {
            assert_eq!(id.0[0].as_str(), "abc");
        }
        _ => panic!(),
    }

    match p_expression("@abc").unwrap() {
        Expression::Ref(inner, _) => {
            assert_sid_expression(inner.as_ref(), "abc");
        }
        _ => panic!()
    }

    match p_expression("~abc").unwrap() {
        Expression::RefMut(inner, _) => {
            assert_sid_expression(inner.as_ref(), "abc");
        }
        _ => panic!()
    }

    match p_expression("abc@").unwrap() {
        Expression::Deref(inner, _) => {
            assert_sid_expression(inner.as_ref(), "abc");
        }
        _ => panic!()
    }

    match p_expression("abc@@").unwrap() {
        Expression::Deref(inner, _) => {
            match inner.as_ref() {
                &Expression::Deref(ref inner, _) => {
                    assert_sid_expression(inner.as_ref(), "abc");
                }
                _ => panic!()
            }
        }
        _ => panic!()
    }

    match p_expression("abc~").unwrap() {
        Expression::DerefMut(inner, _) => {
            assert_sid_expression(inner.as_ref(), "abc");
        }
        _ => panic!()
    }

    match p_expression("[abc]").unwrap() {
        Expression::Array(inner, _) => {
            assert_sid_expression(inner.as_ref(), "abc");
        }
        _ => panic!()
    }

    match p_expression("abc[def]").unwrap() {
        Expression::ArrayIndex(arr, index, _) => {
            assert_sid_expression(arr.as_ref(), "abc");
            assert_sid_expression(index.as_ref(), "def");
        }
        _ => panic!()
    }

    match p_expression("(abc; 42)").unwrap() {
        Expression::ProductRepeated(inner, Repetition::Literal(42, _), _) => {
            assert_sid_expression(inner.as_ref(), "abc");
        }
        _ => panic!()
    }

    match p_expression("()").unwrap() {
        Expression::ProductAnon(inners, _) => {
            assert_eq!(inners.len(), 0);
        }
        _ => panic!(),
    }

    match p_expression("(abc)").unwrap() {
        Expression::ProductAnon(inners, _) => {
            assert_eq!(inners[0].0.len(), 0);
            assert_sid_expression(&inners[0].1, "abc");
        }
        _ => panic!(),
    }

    match p_expression("(abc, def)").unwrap() {
        Expression::ProductAnon(inners, _) => {
            assert_eq!(inners[0].0.len(), 0);
            assert_sid_expression(&inners[0].1, "abc");
            assert_eq!(inners[1].0.len(), 0);
            assert_sid_expression(&inners[1].1, "def");
        }
        _ => panic!(),
    }

    match p_expression("(abc = def)").unwrap() {
        Expression::ProductNamed(triples, _) => {
            assert_eq!(triples[0].0, &[][..]);
            assert_sid(&triples[0].1, "abc");
            assert_sid_expression(&triples[0].2, "def");
        }
        _ => panic!(),
    }

    match p_expression("(abc = def, ghi = jkl)").unwrap() {
        Expression::ProductNamed(triples, _) => {
            assert_eq!(triples[0].0, &[][..]);
            assert_sid(&triples[0].1, "abc");
            assert_sid_expression(&triples[0].2, "def");
            assert_eq!(triples[1].0, &[][..]);
            assert_sid(&triples[1].1, "ghi");
            assert_sid_expression(&triples[1].2, "jkl");
        }
        _ => panic!(),
    }

    match p_expression("(#[foo]{abc = def})").unwrap() {
        Expression::ProductNamed(triples, _) => {
            assert_sid_attr(&triples[0].0[0], "foo");
            assert_sid(&triples[0].1, "abc");
            assert_sid_expression(&triples[0].2, "def");
        }
        _ => panic!(),
    }

    match p_expression("(#[foo]#[bar]{abc = def})").unwrap() {
        Expression::ProductNamed(triples, _) => {
            assert_sid_attr(&triples[0].0[0], "foo");
            assert_sid_attr(&triples[0].0[1], "bar");
            assert_sid(&triples[0].1, "abc");
            assert_sid_expression(&triples[0].2, "def");
        }
        _ => panic!(),
    }

    match p_expression("abc.def").unwrap() {
        Expression::ProductAccessNamed(accessee, field, _) => {
            assert_sid_expression(&accessee, "abc");
            assert_sid(&field, "def");
        }
        _ => panic!()
    }

    match p_expression("abc.0").unwrap() {
        Expression::ProductAccessAnon(accessee, 0, _) => {
            assert_sid_expression(&accessee, "abc");
        }
        _ => panic!()
    }

    match p_expression("{}").unwrap() {
        Expression::Block(inner, _) => {
            assert_eq!(inner.len(), 0);
        }
        _ => panic!()
    }

    match p_expression("{abc}").unwrap() {
        Expression::Block(inner, _) => {
            assert_eq!(inner.len(), 1);
            assert_eq!(inner[0].0.len(), 0);
            assert_sid_expression(&inner[0].1, "abc");
        }
        _ => panic!()
    }

    match p_expression("{abc; def}").unwrap() {
        Expression::Block(inner, _) => {
            assert_eq!(inner.len(), 2);
            assert_eq!(inner[0].0.len(), 0);
            assert_sid_expression(&inner[0].1, "abc");
            assert_eq!(inner[1].0.len(), 0);
            assert_sid_expression(&inner[1].1, "def");
        }
        _ => panic!()
    }

    match p_expression("{#[foo]{abc}; #[bar]#[baz]{def}}").unwrap() {
        Expression::Block(inner, _) => {
            assert_eq!(inner.len(), 2);
            assert_eq!(inner[0].0.len(), 1);
            assert_sid_expression(&inner[0].1, "abc");
            assert_eq!(inner[1].0.len(), 2);
            assert_sid_expression(&inner[1].1, "def");
        }
        _ => panic!()
    }

    match p_expression("() -> xyz {}").unwrap() {
        Expression::FunLiteral(FunLiteral(args, ret_type, body), _) => {
            assert_eq!(args.len(), 0);
            assert_sid_type(&ret_type, "xyz");
            assert_eq!(body.len(), 0);
        }
        _ => panic!(),
    }

    match p_expression("abc()").unwrap() {
        Expression::FunApplicationAnon(fun, args, _) => {
            assert_sid_expression(&fun, "abc");
            assert_eq!(args.len(), 0);
        }
        _ => panic!()
    }

    match p_expression("abc(def = ghi)").unwrap() {
        Expression::FunApplicationNamed(fun, args, _) => {
            assert_sid_expression(&fun, "abc");
            assert_eq!(args[0].0.len(), 0);
            assert_sid(&args[0].1, "def");
            assert_sid_expression(&args[0].2, "ghi");
        }
        _ => panic!()
    }

    match p_expression("<abc> => xyz").unwrap() {
        Expression::Generic(args, exp, _) => {
            assert_eq!(args[0].0.len(), 0);
            assert_sid(&args[0].1, "abc");
            assert_sid_expression(&exp, "xyz");
        }
        _ => panic!()
    }

    match p_expression("<abc, def> => xyz").unwrap() {
        Expression::Generic(args, exp, _) => {
            assert_eq!(args[0].0.len(), 0);
            assert_sid(&args[0].1, "abc");
            assert_eq!(args[1].0.len(), 0);
            assert_sid(&args[1].1, "def");
            assert_sid_expression(&exp, "xyz");
        }
        _ => panic!()
    }

    match p_expression("xyz<abc>").unwrap() {
        Expression::TypeApplicationAnon(id, args, _) => {
            assert_sid_id(&id, "xyz");
            assert_sid_type(&args[0].1, "abc");
        }
        _ => panic!(),
    }

    match p_expression("xyz<abc, def>").unwrap() {
        Expression::TypeApplicationAnon(id, args, _) => {
            assert_sid_id(&id, "xyz");
            assert_sid_type(&args[0].1, "abc");
            assert_sid_type(&args[1].1, "def");
        }
        _ => panic!(),
    }

    match p_expression("xyz<abc = def>").unwrap() {
        Expression::TypeApplicationNamed(id, triples, _) => {
            assert_sid_id(&id, "xyz");
            assert_eq!(triples[0].0.len(), 0);
            assert_sid(&triples[0].1, "abc");
            assert_sid_type(&triples[0].2, "def");
        }
        _ => panic!(),
    }

    match p_expression("xyz<abc = def, ghi = jkl>").unwrap() {
        Expression::TypeApplicationNamed(id, triples, _) => {
            assert_sid_id(&id, "xyz");
            assert_eq!(triples[0].0.len(), 0);
            assert_sid(&triples[0].1, "abc");
            assert_sid_type(&triples[0].2, "def");
            assert_eq!(triples[1].0.len(), 0);
            assert_sid(&triples[1].1, "ghi");
            assert_sid_type(&triples[1].2, "jkl");
        }
        _ => panic!(),
    }

    match p_expression("xyz<#[foo]{abc}>").unwrap() {
        Expression::TypeApplicationAnon(id, args, _) => {
            assert_sid_id(&id, "xyz");
            assert_sid_type(&args[0].1, "abc");
        }
        _ => panic!(),
    }

    match p_expression("xyz<#[foo]{abc = def}>").unwrap() {
        Expression::TypeApplicationNamed(id, triples, _) => {
            assert_sid_id(&id, "xyz");
            assert_sid_attr(&triples[0].0[0], "foo");
            assert_sid(&triples[0].1, "abc");
            assert_sid_type(&triples[0].2, "def");
        }
        _ => panic!(),
    }

    match p_expression("xyz<#[foo]#[bar]{abc = def}>").unwrap() {
        Expression::TypeApplicationNamed(id, triples, _) => {
            assert_sid_id(&id, "xyz");
            assert_sid_attr(&triples[0].0[0], "foo");
            assert_sid_attr(&triples[0].0[1], "bar");
            assert_sid(&triples[0].1, "abc");
            assert_sid_type(&triples[0].2, "def");
        }
        _ => panic!(),
    }

    match p_expression("abc as def").unwrap() {
        Expression::Cast(exp, the_type, _) => {
            assert_sid_expression(&exp, "abc");
            assert_sid_type(&the_type, "def");
        }
        _ => panic!()
    }

    match p_expression("abc && def").unwrap() {
        Expression::LAnd(lhs, rhs, _) => {
            assert_sid_expression(&lhs, "abc");
            assert_sid_expression(&rhs, "def");
        }
        _ => panic!()
    }

    match p_expression("abc || def").unwrap() {
        Expression::LOr(lhs, rhs, _) => {
            assert_sid_expression(&lhs, "abc");
            assert_sid_expression(&rhs, "def");
        }
        _ => panic!()
    }

    match p_expression("abc = def").unwrap() {
        Expression::Assignment(lhs, rhs, _) => {
            assert_sid_lvalue(&lhs, "abc");
            assert_sid_expression(&rhs, "def");
        }
        _ => panic!()
    }

    match p_expression("val _").unwrap() {
        Expression::Val(PatternIrref::Blank(_), rhs, _) => {
            assert_eq!(rhs, None)
        }
        _ => panic!()
    }

    match p_expression("val _ = def").unwrap() {
        Expression::Val(PatternIrref::Blank(_), rhs, _) => {
            assert_sid_expression(rhs.unwrap().as_ref(), "def");
        }
        _ => panic!()
    }

    match p_expression("if a {}").unwrap() {
        Expression::If(cond, if_block, else_block, _) => {
            assert_sid_expression(&cond.as_ref(), "a");
            assert_eq!(if_block.len(), 0);
            assert_eq!(else_block, None);
        }
        _ => panic!()
    }

    match p_expression("if a {} else {}").unwrap() {
        Expression::If(cond, if_block, else_block, _) => {
            assert_sid_expression(&cond.as_ref(), "a");
            assert_eq!(if_block.len(), 0);
            assert_eq!(else_block.unwrap().len(), 0);
        }
        _ => panic!()
    }

    match p_expression("if a {} else if b {}").unwrap() {
        Expression::If(cond, if_block, else_block, _) => {
            assert_sid_expression(&cond.as_ref(), "a");
            assert_eq!(if_block.len(), 0);
            match else_block.unwrap()[0].1 {
                Expression::If(ref cond, ref if_block, ref else_block, _) => {
                    assert_sid_expression(cond.as_ref(), "b");
                    assert_eq!(if_block.len(), 0);
                    assert_eq!(*else_block, None);
                }
                _ => panic!()
            }
        }
        _ => panic!()
    }

    match p_expression("if a {} else if b {} else {}").unwrap() {
        Expression::If(cond, if_block, else_block, _) => {
            assert_sid_expression(&cond.as_ref(), "a");
            assert_eq!(if_block.len(), 0);
            match else_block.unwrap()[0].1 {
                Expression::If(ref cond, ref if_block, ref mut else_block, _) => {
                    assert_sid_expression(cond.as_ref(), "b");
                    assert_eq!(if_block.len(), 0);
                    assert_eq!(else_block.take().unwrap().len(), 0);
                }
                _ => panic!()
            }
        }
        _ => panic!()
    }

    match p_expression("case abc {}").unwrap() {
        Expression::Case(matcher, branches, _) => {
            assert_sid_expression(&matcher, "abc");
            assert_eq!(branches.len(), 0);
        }
        _ => panic!()
    }

    match p_expression("case abc {_{}_{}}").unwrap() {
        Expression::Case(matcher, branches, _) => {
            assert_sid_expression(&matcher, "abc");
            assert_eq!(branches.len(), 2);
        }
        _ => panic!()
    }

    match p_expression("case abc {#[foo]{_{}}}").unwrap() {
        Expression::Case(matcher, branches, _) => {
            assert_sid_expression(&matcher, "abc");
            assert_eq!(branches.len(), 1);
            assert_eq!(branches[0].0.len(), 1);
        }
        _ => panic!()
    }

    match p_expression("while abc {}").unwrap() {
        Expression::While(cond, block, _) => {
            assert_sid_expression(&cond, "abc");
            assert_eq!(block.len(), 0);
        }
        _ => panic!()
    }

    match p_expression("loop abc {}").unwrap() {
        Expression::Loop(matcher, branches, _) => {
            assert_sid_expression(&matcher, "abc");
            assert_eq!(branches.len(), 0);
        }
        _ => panic!()
    }

    match p_expression("loop abc {_{}_{}}").unwrap() {
        Expression::Loop(matcher, branches, _) => {
            assert_sid_expression(&matcher, "abc");
            assert_eq!(branches.len(), 2);
        }
        _ => panic!()
    }

    match p_expression("loop abc {#[foo]{_{}}}").unwrap() {
        Expression::Loop(matcher, branches, _) => {
            assert_sid_expression(&matcher, "abc");
            assert_eq!(branches.len(), 1);
            assert_eq!(branches[0].0.len(), 1);
        }
        _ => panic!()
    }

    match p_expression("return").unwrap() {
        Expression::Return(val, _) => {
            assert_eq!(val, None);
        }
        _ => panic!()
    }

    match p_expression("return abc").unwrap() {
        Expression::Return(val, _) => {
            assert_sid_expression(&val.unwrap(), "abc");
        }
        _ => panic!()
    }

    match p_expression("break").unwrap() {
        Expression::Break(val, _) => {
            assert_eq!(val, None);
        }
        _ => panic!()
    }

    match p_expression("break abc").unwrap() {
        Expression::Break(val, _) => {
            assert_sid_expression(&val.unwrap(), "abc");
        }
        _ => panic!()
    }
}

// #[derive(Debug, PartialEq, Eq, Clone)]
// pub enum UsePrefix<'i> {
//     Mod(Pair<'i, Rule>),
//     Dep(Pair<'i, Rule>),
//     Magic(Pair<'i, Rule>),
//     None
// }
//
// fn pair_to_use_prefix<'i>(pair: Pair<'i, Rule>) -> UsePrefix<'i> {
//     debug_assert!(pair.as_rule() == Rule::use_prefix);
//     let p = pair.clone().into_inner().next();
//
//     match p {
//         None => UsePrefix::None,
//         Some(p) => match p.as_rule() {
//             Rule::_mod => UsePrefix::Mod(pair),
//             Rule::_dep => UsePrefix::Dep(pair),
//             Rule::_magic => UsePrefix::Magic(pair),
//             _ => unreachable!(),
//         }
//     }
// }
//
// pub fn p_use_prefix<'i>(input: &'i str) -> PestResult<UsePrefix<'i>> {
//     LookParser::parse(Rule::use_prefix, input).map(|mut pairs| pair_to_use_prefix(pairs.next().unwrap()))
// }
//
// #[test]
// fn test_use_prefix() {
//     match p_use_prefix("mod::").unwrap() {
//         UsePrefix::Mod(_) => {}
//         _ => panic!()
//     }
//
//     match p_use_prefix("dep::").unwrap() {
//         UsePrefix::Dep(_) => {}
//         _ => panic!()
//     }
//
//     match p_use_prefix("magic::").unwrap() {
//         UsePrefix::Magic(_) => {}
//         _ => panic!()
//     }
//
//     match p_use_prefix("").unwrap() {
//         UsePrefix::None => {}
//         _ => panic!()
//     }
// }
//
// #[derive(Debug, PartialEq, Eq, Clone)]
// pub enum UseTree<'i> {
//     IdLeaf(SimpleIdentifier<'i>, Pair<'i, Rule>),
//     SelfLeaf(Pair<'i, Rule>),
//     IdRenamedLeaf(SimpleIdentifier<'i>, SimpleIdentifier<'i>, Pair<'i, Rule>),
//     SelfRenamedLeaf(SimpleIdentifier<'i>, Pair<'i, Rule>),
//     IdBranch(SimpleIdentifier<'i>, Vec<(Vec<Attribute<'i>>, UseTree<'i>)>, Pair<'i, Rule>),
//     SuperBranch(Vec<(Vec<Attribute<'i>>, UseTree<'i>)>, Pair<'i, Rule>),
// }
//
// fn pair_to_use_branch<'i>(p: Pair<'i, Rule>) -> Vec<(Vec<Attribute<'i>>, UseTree<'i>)> {
//     debug_assert!(p.as_rule() == Rule::use_branch);
//
//     let mut branches = vec![];
//
//     for pair in p.into_inner() {
//         match pair.as_rule() {
//             Rule::use_tree => {
//                 branches.push((vec![], pair_to_use_tree(pair)));
//             }
//             Rule::attributed_use_tree => {
//                 let mut attrs = vec![];
//                 let mut tree = None;
//                 for inner_pair in pair.into_inner() {
//                     match inner_pair.as_rule() {
//                         Rule::attribute => attrs.push(pair_to_attribute(inner_pair)),
//                         Rule::use_tree => tree = Some(pair_to_use_tree(inner_pair)),
//                         _ => unreachable!()
//                     }
//                 }
//                 branches.push((attrs, tree.unwrap()));
//             }
//             _ => unreachable!()
//         }
//     }
//
//     return branches;
// }
//
// fn pair_to_use_tree<'i>(p: Pair<'i, Rule>) -> UseTree<'i> {
//     debug_assert!(p.as_rule() == Rule::use_tree);
//     let mut pairs = p.clone().into_inner().peekable();
//
//     let pair = pairs.next().unwrap();
//     match pair.as_rule() {
//         Rule::_self => {
//             let is_rename = pairs.peek().is_some();
//             if is_rename {
//                 assert!(pairs.next().unwrap().as_rule() == Rule::_as);
//                 UseTree::SelfRenamedLeaf(pair_to_simple_identifier(pairs.next().unwrap()), p)
//             } else {
//                 UseTree::SelfLeaf(p)
//             }
//         },
//         Rule::sid => {
//             let sid = pair_to_simple_identifier(pair);
//             match pairs.next() {
//                 None => UseTree::IdLeaf(sid, p),
//                 Some(pair) => {
//                     match pair.as_rule() {
//                         Rule::scope => UseTree::IdBranch(sid, pair_to_use_branch(pairs.next().unwrap()), p),
//                         Rule::_as => UseTree::IdRenamedLeaf(sid, pair_to_simple_identifier(pairs.next().unwrap()), p),
//                         _ => unreachable!()
//                     }
//                 }
//             }
//         }
//         Rule::_super => {
//             debug_assert!(pairs.next().unwrap().as_rule() == Rule::scope);
//             UseTree::SuperBranch(pair_to_use_branch(pairs.next().unwrap()), p)
//         }
//         _ => unreachable!(),
//     }
// }
//
// pub fn p_use_tree<'i>(input: &'i str) -> PestResult<UseTree<'i>> {
//     LookParser::parse(Rule::use_tree, input).map(|mut pairs| pair_to_use_tree(pairs.next().unwrap()))
// }
//
// #[test]
// fn test_use_tree() {
//     match p_use_tree("abc").unwrap() {
//         UseTree::IdLeaf(sid, _) => assert_sid(&sid, "abc"),
//         _ => panic!()
//     }
//
//     match p_use_tree("super::{foo::bar, self}").unwrap() {
//         UseTree::SuperBranch(mut branches, _) => {
//             match branches.pop().unwrap() {
//                 (attrs, UseTree::SelfLeaf(_)) => {
//                     assert_eq!(attrs.len(), 0);
//                 }
//                 _ => panic!()
//             }
//
//             match branches.pop().unwrap() {
//                 (attrs, UseTree::IdBranch(sid, mut branches, _)) => {
//                     assert_eq!(attrs.len(), 0);
//                     assert_sid(&sid, "foo");
//                     match branches.pop().unwrap() {
//                         (attrs, UseTree::IdLeaf(sid, _)) => {
//                             assert_eq!(attrs.len(), 0);
//                             assert_sid(&sid, "bar");
//                         }
//                         _ => panic!()
//                     }
//                 }
//                 _ => panic!()
//             }
//         }
//         _ => panic!()
//     }
//
//     match p_use_tree("abc::{#[foo]#[bar]{def}}").unwrap() {
//         UseTree::IdBranch(sid, mut branches, _) => {
//             assert_sid(&sid, "abc");
//             match branches.pop().unwrap() {
//                 (attrs, UseTree::IdLeaf(sid, _)) => {
//                     assert_sid(&sid, "def");
//                     assert_eq!(attrs.len(), 2)
//                 }
//                 _ => panic!(),
//             }
//         }
//         _ => panic!()
//     }
//
//     match p_use_tree("super::{foo as bar, self as baz}").unwrap() {
//         UseTree::SuperBranch(mut branches, _) => {
//             match branches.pop().unwrap() {
//                 (attrs, UseTree::SelfRenamedLeaf(sid, _)) => {
//                     assert_eq!(attrs.len(), 0);
//                     assert_sid(&sid, "baz");
//                 }
//                 _ => panic!()
//             }
//
//             match branches.pop().unwrap() {
//                 (attrs, UseTree::IdRenamedLeaf(sid, new_name, _)) => {
//                     assert_eq!(attrs.len(), 0);
//                     assert_sid(&sid, "foo");
//                     assert_sid(&new_name, "bar");
//                 }
//                 _ => panic!()
//             }
//         }
//         _ => panic!()
//     }
// }
//
// #[derive(Debug, PartialEq, Eq, Clone)]
// pub enum FfiLanguage {
//     C
// }
//
// #[derive(Debug, PartialEq, Eq, Clone)]
// pub enum FfiItem<'i> {
//     Type(bool, SimpleIdentifier<'i>, Pair<'i, Rule>),
//     Val(bool, SimpleIdentifier<'i>, Type<'i>, Pair<'i, Rule>),
// }
//
// fn pair_to_ffi_item<'i>(p: Pair<'i, Rule>) -> FfiItem<'i> {
//     debug_assert!(p.as_rule() == Rule::ffi_item);
//     let pair = p.clone().into_inner().next().unwrap();
//
//     match pair.as_rule() {
//         Rule::ffi_type => {
//             let mut pairs = pair.into_inner().peekable();
//             let public = pairs.peek().unwrap().as_rule() == Rule::_pub;
//
//             if public {
//                 pairs.next();
//             }
//
//             assert!(pairs.next().unwrap().as_rule() == Rule::_type_kw);
//             return FfiItem::Type(public, pair_to_simple_identifier(pairs.next().unwrap()), p);
//         }
//         Rule::ffi_val => {
//             let mut pairs = pair.into_inner().peekable();
//             let public = pairs.peek().unwrap().as_rule() == Rule::_pub;
//
//             if public {
//                 pairs.next();
//             }
//
//             assert!(pairs.next().unwrap().as_rule() == Rule::_val);
//             let sid = pair_to_simple_identifier(pairs.next().unwrap());
//             return FfiItem::Val(public, sid, pair_to_type(pairs.next().unwrap()), p);
//         }
//         _ => unreachable!()
//     }
// }
//
// #[derive(Debug, PartialEq, Eq, Clone)]
// pub enum Item<'i> {
//     Use(bool, UsePrefix<'i>, UseTree<'i>, Pair<'i, Rule>),
//     Type(bool, SimpleIdentifier<'i>, TypeDef<'i>, Pair<'i, Rule>),
//     Val(bool, Pattern<'i>, Expression<'i>, Pair<'i, Rule>),
//     FfiBlock(FfiLanguage, Vec<(Vec<Attribute<'i>>, FfiItem<'i>)>, Pair<'i, Rule>),
// }
//
// fn pair_to_use_item<'i>(p: Pair<'i, Rule>) -> Item<'i> {
//     debug_assert!(p.as_rule() == Rule::use_item);
//     let mut pairs = p.clone().into_inner().peekable();
//     let public = pairs.peek().unwrap().as_rule() == Rule::_pub;
//
//     if public {
//         pairs.next();
//     }
//
//     assert!(pairs.next().unwrap().as_rule() == Rule::_use);
//
//     let prefix = pair_to_use_prefix(pairs.next().unwrap());
//     let tree = pair_to_use_tree(pairs.next().unwrap());
//
//     Item::Use(public, prefix, tree, p)
// }
//
// fn pair_to_type_item<'i>(p: Pair<'i, Rule>) -> Item<'i> {
//     debug_assert!(p.as_rule() == Rule::type_item);
//     let mut pairs = p.clone().into_inner().peekable();
//     let public = pairs.peek().unwrap().as_rule() == Rule::_pub;
//
//     if public {
//         pairs.next();
//     }
//
//     assert!(pairs.next().unwrap().as_rule() == Rule::_type_kw);
//
//     let sid = pair_to_simple_identifier(pairs.next().unwrap());
//     let type_def = pair_to_type_def(pairs.next().unwrap());
//
//     Item::Type(public, sid, type_def, p)
// }
//
// fn pair_to_val_item<'i>(p: Pair<'i, Rule>) -> Item<'i> {
//     debug_assert!(p.as_rule() == Rule::val_item);
//     let mut pairs = p.clone().into_inner().peekable();
//     let public = pairs.peek().unwrap().as_rule() == Rule::_pub;
//
//     if public {
//         pairs.next();
//     }
//
//     assert!(pairs.next().unwrap().as_rule() == Rule::_val);
//
//     let pattern = pair_to_pattern(pairs.next().unwrap());
//     let val = pair_to_expression(pairs.next().unwrap());
//
//     Item::Val(public, pattern, val, p)
// }
//
// fn pair_to_ffi_block<'i>(p: Pair<'i, Rule>) -> Item<'i> {
//     debug_assert!(p.as_rule() == Rule::ffi_block);
//     let mut pairs = p.clone().into_inner();
//
//     assert!(pairs.next().unwrap().as_rule() == Rule::_ffi);
//     assert!(pairs.next().unwrap().as_rule() == Rule::ffi_language);
//
//     let mut block_items = vec![];
//     let mut attrs = vec![];
//
//     for pair in pairs {
//         match pair.as_rule() {
//             Rule::attribute => {
//                 attrs.push(pair_to_attribute(pair));
//             }
//             Rule::ffi_item => {
//                 block_items.push((attrs.clone(), pair_to_ffi_item(pair)));
//                 attrs = vec![];
//             }
//             _ => unreachable!()
//         }
//     }
//
//     Item::FfiBlock(FfiLanguage::C, block_items, p)
// }
//
// fn pair_to_item<'i>(p: Pair<'i, Rule>) -> Item<'i> {
//     debug_assert!(p.as_rule() == Rule::item);
//     let pair = p.into_inner().next().unwrap();
//
//     match pair.as_rule() {
//         Rule::use_item => pair_to_use_item(pair),
//         Rule::type_item => pair_to_type_item(pair),
//         Rule::val_item => pair_to_val_item(pair),
//         Rule::ffi_block => pair_to_ffi_block(pair),
//         _ => unreachable!()
//     }
// }
//
// pub fn p_item<'i>(input: &'i str) -> PestResult<Item<'i>> {
//     LookParser::parse(Rule::item, input).map(|mut pairs| pair_to_item(pairs.next().unwrap()))
// }
//
// #[test]
// fn test_item() {
//     match p_item("use foo").unwrap() {
//         Item::Use(false, UsePrefix::None, UseTree::IdLeaf(sid, _), _) => {
//             assert_sid(&sid, "foo");
//         }
//         _ => panic!()
//     }
//
//     match p_item("pub use self").unwrap() {
//         Item::Use(true, UsePrefix::None, UseTree::SelfLeaf(_), _) => {}
//         _ => panic!()
//     }
//
//     match p_item("type foo = bar").unwrap() {
//         Item::Type(false, sid, inner, _) => {
//             assert_sid(&sid, "foo");
//             assert_sid_type_def(&inner, "bar");
//         }
//         _ => panic!()
//     }
//
//     match p_item("pub type foo = bar").unwrap() {
//         Item::Type(true, sid, inner, _) => {
//             assert_sid(&sid, "foo");
//             assert_sid_type_def(&inner, "bar");
//         }
//         _ => panic!()
//     }
//
//     match p_item("val _ = bar").unwrap() {
//         Item::Val(false, Pattern::Blank(_), inner, _) => {
//             assert_sid_expression(&inner, "bar");
//         }
//         _ => panic!()
//     }
//
//     match p_item("pub val _ = bar").unwrap() {
//         Item::Val(true, Pattern::Blank(_), inner, _) => {
//             assert_sid_expression(&inner, "bar");
//         }
//         _ => panic!()
//     }
//
//     match p_item("ffi C {pub type abc val def: ghi}").unwrap() {
//         Item::FfiBlock(FfiLanguage::C, mut items, _) => {
//             match items.pop().unwrap() {
//                 (attrs, FfiItem::Val(false, sid, the_type, _)) => {
//                     assert_eq!(attrs.len(), 0);
//                     assert_sid(&sid, "def");
//                     assert_sid_type(&the_type, "ghi");
//                 }
//                 _ => panic!()
//             }
//
//             match items.pop().unwrap() {
//                 (attrs, FfiItem::Type(true, sid, _)) => {
//                     assert_eq!(attrs.len(), 0);
//                     assert_sid(&sid, "abc");
//                 }
//                 _ => panic!()
//             }
//         }
//         _ => panic!()
//     }
// }
//
// #[derive(Debug, PartialEq, Eq, Clone)]
// pub struct File<'i>(pub Vec<(Vec<Attribute<'i>>, Item<'i>)>);
//
// fn pair_to_file<'i>(p: Pair<'i, Rule>) -> File<'i> {
//     debug_assert!(p.as_rule() == Rule::file);
//
//     let mut items = vec![];
//
//     for pair in p.clone().into_inner() {
//         debug_assert!(pair.as_rule() == Rule::file_item);
//         let mut attrs = vec![];
//
//         for pair in pair.into_inner() {
//             match pair.as_rule() {
//                 Rule::attribute => {
//                     attrs.push(pair_to_attribute(pair));
//                 }
//                 Rule::item => {
//                     items.push((attrs.clone(), pair_to_item(pair)));
//                 }
//                 _ => unreachable!()
//             }
//         }
//     }
//
//     File(items)
// }
//
// pub fn p_file<'i>(input: &'i str) -> PestResult<File<'i>> {
//     LookParser::parse(Rule::file, input).map(|mut pairs| pair_to_file(pairs.next().unwrap()))
// }
//
// #[test]
// fn test_file() {
//     let File(mut items) = p_file("val _ = foo #[foo] { type bar = baz }").unwrap();
//
//     match items.pop().unwrap() {
//         (attrs, Item::Type(false, sid, type_def, _)) => {
//             assert_eq!(attrs.len(), 1);
//             assert_sid(&sid, "bar");
//             assert_sid_type_def(&type_def, "baz");
//         }
//         _ => panic!()
//     }
//
//     match items.pop().unwrap() {
//         (attrs, Item::Val(false, Pattern::Blank(_), inner, _)) => {
//             assert_eq!(attrs.len(), 0);
//             assert_sid_expression(&inner, "foo");
//         }
//         _ => panic!()
//     }
// }
//
// // Well-known types: Void, Bool, U8, I8, U16, I16, U32, I32, U64, I64, USize, ISize, F32, F64
// //
// // List of magic:
// //
// // - `sizeof` macro
// // - modules for functions for the well-known types (e.g. magic::i32::add, magic::bool::not)
// // And some magic that can be added later as needed
// // - `alignof` macro (can be added later)
// // - stringify macro for features (also parse_intify, parse_floatify and a bool macro)
// //
// // List of attributes:
// //
// // - conditional compilation (`cond`)
// // - repr (C)
// // - test
