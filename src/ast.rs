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

fn pair_to_named_product_field_type<'i>(p: Pair<'i, Rule>) -> (Vec<Attribute<'i>>, SimpleIdentifier<'i>, Type<'i>) {
    debug_assert!(p.as_rule() == Rule::named_product_field_type);

    let mut attrs = vec![];

    for pair in p.into_inner() {
        match pair.as_rule() {
            Rule::attribute => {
                attrs.push(pair_to_attribute(pair));
            }

            Rule::actual_named_product_field_type => {
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
                        let mut named_fields = pair.into_inner().map(pair_to_named_product_field_type).collect();
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
                        let mut args = pairs.next().unwrap().into_inner().map(pair_to_named_product_field_type).collect();
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

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Summand<'i> {
    Empty(SimpleIdentifier<'i>, Pair<'i, Rule>),
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

fn pair_to_type_level_arg<'i>(p: Pair<'i, Rule>) -> (Vec<Attribute<'i>>, SimpleIdentifier<'i>) {
    debug_assert!(p.as_rule() == Rule::type_level_arg);

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
    debug_assert!(p.as_rule() == Rule::actual_summand);

    let mut pairs = p.clone().into_inner().peekable();

    let sid = pair_to_simple_identifier(pairs.next().unwrap());

    match pairs.next() {
        None => Summand::Empty(sid, p),

        Some(pair) => {
            match pair.as_rule() {
                Rule::product_anon_type => {
                    Summand::Anon(sid, pair.into_inner().map(pair_to_type).collect(), p)
                }

                Rule::product_named_type => {
                    Summand::Named(sid, pair.into_inner().map(pair_to_named_product_field_type).collect(), p)
                }

                _ => unreachable!()
            }
        }
    }
}

fn pair_to_summand<'i>(p: Pair<'i, Rule>) -> (Vec<Attribute<'i>>, Summand<'i>) {
    debug_assert!(p.as_rule() == Rule::summand);

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
                Summand::Empty(ref sid, _) => {
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
                Summand::Empty(ref sid, _) => {
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
                Summand::Empty(ref sid, _) => {
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
                Summand::Empty(ref sid, _) => {
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
                Summand::Empty(ref sid, _) => {
                    assert_sid(sid, "A");
                }
                _ => panic!()
            }
            assert_eq!(summands[1].0, &[][..]);
            match summands[1].1 {
                Summand::Empty(ref sid, _) => {
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
                Summand::Anon( ref sid, ref types, _) => {
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
                Summand::Named(ref sid, ref args, _) => {
                    assert_sid(sid, "A");
                    assert_eq!(args.len(), 1);
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
    SummandEmpty(SimpleIdentifier<'i>, Pair<'i, Rule>),
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
            &Pattern::SummandEmpty(_, ref pair) => pair,
            &Pattern::SummandAnon(_, _, ref pair) => pair,
            &Pattern::SummandNamed(_, _, ref pair) => pair,
        }
    }

    pub fn is_refutable(&self) -> bool {
        match self {
            &Pattern::Blank(_) => false,
            &Pattern::Id(_, _, _, _) => false,
            &Pattern::Ptr(ref inner, _) => inner.as_ref().is_refutable(),
            &Pattern::ProductAnon(ref inners, _) => {
                inners.iter().all(|&(_, ref pattern)| pattern.is_refutable())
            }
            &Pattern::ProductNamed(ref inners, _) => {
                inners.iter().all(|&(_, _, ref pattern)| pattern.is_refutable())
            }
            _ => true
        }
    }
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
    ProductAccessAnon(Box<Expression<'i>>, Literal<'i>, Pair<'i, Rule>),
    ProductAccessNamed(Box<Expression<'i>>, SimpleIdentifier<'i>, Pair<'i, Rule>),
    FunLiteral(Vec<(Vec<Attribute<'i>>, Pattern<'i>)>, Type<'i>, Vec<Expression<'i>>, Pair<'i, Rule>),
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
    Assignment(Box<Expression<'i>>, Box<Expression<'i>>, Pair<'i, Rule>),
    Val(Pattern<'i>, Option<Box<Expression<'i>>>, Pair<'i, Rule>),
    If(Box<Expression<'i>>, Vec<Expression<'i>>, Option<Vec<Expression<'i>>>, Pair<'i, Rule>),
    Case(Box<Expression<'i>>, Vec<(Vec<Attribute<'i>>, Pattern<'i>, Vec<Expression<'i>>)>, Pair<'i, Rule>),
    While(Box<Expression<'i>>, Vec<Expression<'i>>, Pair<'i, Rule>),
    Loop(Box<Expression<'i>>, Vec<(Vec<Attribute<'i>>, Pattern<'i>, Vec<Expression<'i>>)>, Pair<'i, Rule>),
    Return(Option<Box<Expression<'i>>>, Pair<'i, Rule>),
    Break(Option<Box<Expression<'i>>>, Pair<'i, Rule>),
}

impl<'i> Expression<'i> {
    pub fn attributes(&self) -> &Vec<Attribute> {
        match self {
            &Expression::Id(ref attrs, _, _) => attrs,
            &Expression::Literal(ref attrs, _, _) => attrs,
            &Expression::MacroInv(ref attrs, _, _) => attrs,
            &Expression::Ref(ref attrs, _, _) => attrs,
            &Expression::RefMut(ref attrs, _, _) => attrs,
            &Expression::Deref(ref attrs, _, _) => attrs,
            &Expression::DerefMut(ref attrs, _, _) => attrs,
            &Expression::Array(ref attrs, _, _) => attrs,
            &Expression::ArrayIndex(ref attrs, _, _, _) => attrs,
            &Expression::ProductRepeated(ref attrs, _, _, _) => attrs,
            &Expression::ProductAnon(ref attrs, _, _) => attrs,
            &Expression::ProductNamed(ref attrs, _, _) => attrs,
            &Expression::ProductAccessAnon(ref attrs, _, _, _) => attrs,
            &Expression::ProductAccessNamed(ref attrs, _, _, _) => attrs,
            &Expression::FunLiteral(ref attrs, _, _, _, _) => attrs,
            &Expression::FunApplicationAnon(ref attrs, _, _, _) => attrs,
            &Expression::FunApplicationNamed(ref attrs, _, _, _) => attrs,
            &Expression::Generic(ref attrs, _, _, _) => attrs,
            &Expression::TypeApplicationAnon(ref attrs, _, _, _) => attrs,
            &Expression::TypeApplicationNamed(ref attrs, _, _, _) => attrs,
            &Expression::Cast(ref attrs, _, _, _) => attrs,
            &Expression::LAnd(ref attrs, _, _, _) => attrs,
            &Expression::LOr(ref attrs, _, _, _) => attrs,
            &Expression::Assignment(ref attrs, _, _, _) => attrs,
            &Expression::Val(ref attrs, _, _, _) => attrs,
            &Expression::If(ref attrs, _, _, _, _) => attrs,
            &Expression::Case(ref attrs, _, _, _) => attrs,
            &Expression::While(ref attrs, _, _, _) => attrs,
            &Expression::Loop(ref attrs, _, _, _) => attrs,
            &Expression::Return(ref attrs, _, _) => attrs,
            &Expression::Break(ref attrs, _, _) => attrs,
        }
    }

    pub fn pair(&self) -> &Pair<'i, Rule> {
        match self {
            &Expression::Id(_, _, ref pair) => pair,
            &Expression::Literal(_ , _, ref pair) => pair,
            &Expression::MacroInv(_, _, ref pair) => pair,
            &Expression::Ref(_, _, ref pair) => pair,
            &Expression::RefMut(_, _, ref pair) => pair,
            &Expression::Deref(_, _, ref pair) => pair,
            &Expression::DerefMut(_, _, ref pair) => pair,
            &Expression::Array(_, _, ref pair) => pair,
            &Expression::ArrayIndex(_, _, _, ref pair) => pair,
            &Expression::ProductRepeated(_, _, _, ref pair) => pair,
            &Expression::ProductAnon(_, _,ref pair) => pair,
            &Expression::ProductNamed(_, _, ref pair) => pair,
            &Expression::ProductAccessAnon(_, _, _, ref pair) => pair,
            &Expression::ProductAccessNamed(_, _, _, ref pair) => pair,
            &Expression::FunLiteral(_, _, _, _, ref pair) => pair,
            &Expression::FunApplicationAnon(_, _, _, ref pair) => pair,
            &Expression::FunApplicationNamed(_, _, _, ref pair) => pair,
            &Expression::Generic(_, _, _, ref pair) => pair,
            &Expression::TypeApplicationAnon(_, _, _, ref pair) => pair,
            &Expression::TypeApplicationNamed(_, _, _, ref pair) => pair,
            &Expression::Cast(_, _, _, ref pair) => pair,
            &Expression::LAnd(_, _, _, ref pair) => pair,
            &Expression::LOr(_, _, _, ref pair) => pair,
            &Expression::Assignment(_, _, _, ref pair) => pair,
            &Expression::Val(_, _, _, ref pair) => pair,
            &Expression::If(_, _, _, _, ref pair) => pair,
            &Expression::Case(_, _, _, ref pair) => pair,
            &Expression::While(_, _, _, ref pair) => pair,
            &Expression::Loop(_, _, _, ref pair) => pair,
            &Expression::Return(_, _, ref pair) => pair,
            &Expression::Break(_, _, ref pair) => pair,
        }
    }

    pub fn is_lvalue(&self) -> bool {
        match self {
            &Expression::Id(_, _, _) => true,
            &Expression::DerefMut(_, ref inner, _) => inner.as_ref().is_lvalue(),
            &Expression::ArrayIndex(_, ref inner, _, _) => inner.as_ref().is_lvalue(),
            &Expression::ProductAccessAnon(_, ref inner, _, _) => inner.as_ref().is_lvalue(),
            &Expression::ProductAccessNamed(_, ref inner, _, _) => inner.as_ref().is_lvalue(),
            _ => false,
        }
    }
}

fn pair_to_named_product_field_expression<'i>(p: Pair<'i, Rule>) -> (Vec<Attribute<'i>>, SimpleIdentifier<'i>, Expression<'i>) {
    debug_assert!(p.as_rule() == Rule::named_product_field_expression);

    let mut attrs = vec![];

    for pair in p.into_inner() {
        match pair.as_rule() {
            Rule::attribute => {
                attrs.push(pair_to_attribute(pair));
            }

            Rule::actual_named_product_field_expression => {
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

fn pair_to_block<'i>(p: Pair<'i, Rule>) -> Vec<Expression<'i>> {
    debug_assert!(p.as_rule() == Rule::block);
    p.into_inner().map(pair_to_expression).collect()
}

fn pair_to_if_expression<'i>(p: Pair<'i, Rule>) -> Expression {
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
                Rule::if_expression => return Expression::If(vec![], Box::new(cond), if_block, Some(vec![pair_to_if_expression(pair)]), p),
                Rule::block => return Expression::If(vec![], Box::new(cond), if_block, Some(pair_to_block(pair)), p),
                _ => unreachable!()
            }
        }
        None => return Expression::If(vec![], Box::new(cond), if_block, None, p)
    }
}

fn pair_to_expression<'i>(p: Pair<'i, Rule>) -> Expression<'i> {
    debug_assert!(p.as_rule() == Rule::expression);

    let mut attrs = vec![];
    let mut exp = None;
    let mut pairs = p.clone().into_inner().peekable();

    while let Some(pair) = pairs.next() {
        match pair.as_rule() {
            Rule::attribute => {
                attrs.push(pair_to_attribute(pair));
            }

            Rule::lexpression => {
                let pair = pair.into_inner().next().unwrap();
                match pair.as_rule() {
                    Rule::id => {
                        exp = Some(Expression::Id(vec![], pair_to_identifier(pair), p.clone()));
                        break;
                    }

                    Rule::literal => {
                        exp = Some(Expression::Literal(vec![], pair_to_literal(pair), p.clone()));
                        break;
                    }

                    Rule::macro_invocation => {
                        exp = Some(Expression::MacroInv(vec![], pair_to_macro_invocation(pair), p.clone()));
                        break;
                    }

                    Rule::ref_expression => {
                        exp = Some(Expression::Ref(vec![], Box::new(pair_to_expression(pair.into_inner().next().unwrap())), p.clone()));
                        break;
                    }

                    Rule::ref_mut_expression => {
                        exp = Some(Expression::RefMut(vec![], Box::new(pair_to_expression(pair.into_inner().next().unwrap())), p.clone()));
                        break;
                    }

                    Rule::array_expression => {
                        exp = Some(Expression::Array(vec![], Box::new(pair_to_expression(pair.into_inner().next().unwrap())), p.clone()));
                        break;
                    }

                    Rule::product_repeated_expression => {
                        let mut pairs = pair.into_inner();
                        exp = Some(Expression::ProductRepeated(vec![], Box::new(pair_to_expression(pairs.next().unwrap())), pair_to_repetition(pairs.next().unwrap()), p.clone()));
                        break;
                    }

                    Rule::product_anon_expression => {
                        exp = Some(Expression::ProductAnon(vec![], pair.into_inner().map(pair_to_expression).collect(), p.clone()));
                        break;
                    }

                    Rule::product_named_expression => {
                        let mut named_fields = pair.into_inner().map(pair_to_named_product_field_expression).collect();
                        exp = Some(Expression::ProductNamed(vec![], named_fields, p.clone()));
                        break;
                    }

                    Rule::fun_literal => {
                        let mut pairs = pair.into_inner();
                        let args = pairs.next().unwrap().into_inner().map(pair_to_annotated_pattern).collect();
                        let return_type = pair_to_type(pairs.next().unwrap());
                        let body = pair_to_block(pairs.next().unwrap());
                        exp = Some(Expression::FunLiteral(vec![], args, return_type, body, p.clone()));
                        break;
                    }

                    Rule::generic_expression => {
                        let mut args = vec![];

                        for pair in pair.into_inner() {
                            match pair.as_rule() {
                                Rule::type_level_arg => {
                                    args.push(pair_to_type_level_arg(pair));
                                }

                                Rule::expression => {
                                    exp = Some(Expression::Generic(vec![], args, Box::new(pair_to_expression(pair)), p.clone()));
                                    break;
                                }
                                _ => unreachable!(),
                            }
                        }
                        break;
                    }

                    Rule::type_application_anon => {
                        let mut pairs = pair.into_inner();
                        let id = pair_to_identifier(pairs.next().unwrap());
                        let mut args = pairs.map(pair_to_type).collect();
                        exp = Some(Expression::TypeApplicationAnon(vec![], id, args, p.clone()));
                        break;
                    }

                    Rule::type_application_named => {
                        let mut pairs = pair.into_inner();
                        let id = pair_to_identifier(pairs.next().unwrap());
                        let mut named_type_args = pairs.map(pair_to_named_type_arg).collect();
                        exp = Some(Expression::TypeApplicationNamed(vec![], id, named_type_args, p.clone()));
                        break;
                    }

                    Rule::val_expression => {
                        let mut pairs = pair.into_inner();
                        debug_assert!(pairs.next().unwrap().as_rule() == Rule::_val);
                        let pattern = pair_to_pattern(pairs.next().unwrap());

                        match pairs.next() {
                            Some(pair) => {
                                exp = Some(Expression::Val(vec![], pattern, Some(Box::new(pair_to_expression(pair))), p.clone()));
                                break;
                            }
                            None => {
                                exp = Some(Expression::Val(vec![], pattern, None, p.clone()));
                                break;
                            }
                        }
                    }

                    Rule::if_expression => {
                        exp = Some(pair_to_if_expression(pair));
                        break;
                    }

                    Rule::case_expression => {
                        let mut pairs = pair.into_inner();
                        debug_assert!(pairs.next().unwrap().as_rule() == Rule::_case);
                        let matcher = pair_to_expression(pairs.next().unwrap());

                        let mut branches = vec![];
                        while let Some(pattern_pair) = pairs.next() {
                            branches.push((pair_to_pattern(pattern_pair), pair_to_block(pairs.next().unwrap())));
                        }

                        exp = Some(Expression::Case(vec![], Box::new(matcher), branches, p.clone()));
                        break;
                    }

                    Rule::while_expression => {
                        let mut pairs = pair.into_inner();
                        debug_assert!(pairs.next().unwrap().as_rule() == Rule::_while);
                        let cond = pair_to_expression(pairs.next().unwrap());
                        let block = pair_to_block(pairs.next().unwrap());

                        exp = Some(Expression::While(vec![], Box::new(cond), block, p.clone()));
                        break;
                    }

                    Rule::loop_expression => {
                        let mut pairs = pair.into_inner();
                        debug_assert!(pairs.next().unwrap().as_rule() == Rule::_loop);
                        let matcher = pair_to_expression(pairs.next().unwrap());

                        let mut branches = vec![];
                        while let Some(pattern_pair) = pairs.next() {
                            branches.push((pair_to_pattern(pattern_pair), pair_to_block(pairs.next().unwrap())));
                        }

                        exp = Some(Expression::Loop(vec![], Box::new(matcher), branches, p.clone()));
                        break;
                    }

                    Rule::return_expression => {
                        let mut pairs = pair.into_inner();
                        debug_assert!(pairs.next().unwrap().as_rule() == Rule::_return);

                        match pairs.next() {
                            Some(pair) => {
                                exp = Some(Expression::Return(vec![], Some(Box::new(pair_to_expression(pair))), p.clone()));
                                break;
                            }
                            None => {
                                exp = Some(Expression::Return(vec![], None, p.clone()));
                                break;
                            }
                        }
                    }

                    Rule::break_expression => {
                        let mut pairs = pair.into_inner();
                        debug_assert!(pairs.next().unwrap().as_rule() == Rule::_break);

                        match pairs.next() {
                            Some(pair) => {
                                exp = Some(Expression::Break(vec![], Some(Box::new(pair_to_expression(pair))), p.clone()));
                                break;
                            }
                            None => {
                                exp = Some(Expression::Break(vec![], None, p.clone()));
                                break;
                            }
                        }
                    }

                    _ => unreachable!()
                }
            }
            _ => unreachable!()
        }
    };

    let pair = pairs.next().unwrap();
    debug_assert!(pair.as_rule() == Rule::expression_);

    match pair.into_inner().next() {
        Some(pair) => {
            match pair.as_rule() {
                Rule::deref_ => {
                    return Expression::Deref(attrs, Box::new(exp.unwrap()), p);
                }

                Rule::deref_mut_ => {
                    return Expression::DerefMut(attrs, Box::new(exp.unwrap()), p);
                }

                Rule::array_index_ => {
                    return Expression::ArrayIndex(attrs, Box::new(exp.unwrap()), Box::new(pair_to_expression(pair.into_inner().next().unwrap())), p);
                }

                Rule::product_access_named_ => {
                    return Expression::ProductAccessNamed(attrs, Box::new(exp.unwrap()), pair_to_simple_identifier(pair.into_inner().next().unwrap()), p);
                }

                Rule::product_access_anon_ => {
                    return Expression::ProductAccessAnon(attrs, Box::new(exp.unwrap()), pair_to_literal(pair.into_inner().next().unwrap()), p);
                }

                Rule::product_anon_expression => {
                    return Expression::FunApplicationAnon(attrs, Box::new(exp.unwrap()), pair.into_inner().map(pair_to_expression).collect(), p);
                }

                Rule::product_named_expression => {
                    return Expression::FunApplicationNamed(attrs, Box::new(exp.unwrap()), pair.into_inner().map(pair_to_named_product_field_expression).collect(), p);
                }

                Rule::cast_ => {
                    return Expression::Cast(attrs, Box::new(exp.unwrap()), pair_to_type(pair.into_inner().next().unwrap()), p);
                }

                Rule::land_ => {
                    return Expression::LAnd(attrs, Box::new(exp.unwrap()), Box::new(pair_to_expression(pair.into_inner().next().unwrap())), p);
                }

                Rule::lor_ => {
                    return Expression::LOr(attrs, Box::new(exp.unwrap()), Box::new(pair_to_expression(pair.into_inner().next().unwrap())), p);
                }

                Rule::assignment_ => {
                    return Expression::Assignment(attrs, Box::new(exp.unwrap()), Box::new(pair_to_expression(pair.into_inner().next().unwrap())), p);
                }

                _ => unreachable!()
            }
        }

        None => {
            match exp.unwrap() {
                Expression::Id(_, id, pair) => Expression::Id(attrs, id, pair),
                Expression::Literal(_, lit, pair) => Expression::Literal(attrs, lit, pair),
                Expression::MacroInv(_, inv, pair) => Expression::MacroInv(attrs, inv, pair),
                Expression::Ref(_, inner, pair) => Expression::Ref(attrs, inner, pair),
                Expression::RefMut(_, inner, pair) => Expression::RefMut(attrs, inner, pair),
                Expression::Array(_, inner, pair) => Expression::Array(attrs, inner, pair),
                Expression::ProductRepeated(_, inner, repetition, pair) => Expression::ProductRepeated(attrs, inner, repetition, pair),
                Expression::ProductAnon(_, inners, pair) => Expression::ProductAnon(attrs, inners, pair),
                Expression::ProductNamed(_, inners, pair) => Expression::ProductNamed(attrs, inners, pair),
                Expression::FunLiteral(_, args, return_type, body, pair) => Expression::FunLiteral(attrs, args, return_type, body, pair),
                Expression::Generic(_, args, exp, pair) => Expression::Generic(attrs, args, exp, pair),
                Expression::TypeApplicationAnon(_, id, args, pair) => Expression::TypeApplicationAnon(attrs, id, args, pair),
                Expression::TypeApplicationNamed(_, id, args, pair) => Expression::TypeApplicationNamed(attrs, id, args, pair),
                Expression::Val(_, sid, rhs, pair) => Expression::Val(attrs, sid, rhs, pair),
                Expression::If(_, cond, if_block, else_block, pair) => Expression::If(attrs, cond, if_block, else_block, pair),
                Expression::Case(_, matcher, branches, pair) => Expression::Case(attrs, matcher, branches, pair),
                Expression::While(_, cond, block, pair) => Expression::While(attrs, cond, block, pair),
                Expression::Loop(_, matcher, branches, pair) => Expression::Loop(attrs, matcher, branches, pair),
                Expression::Return(_, val, pair) => Expression::Return(attrs, val, pair),
                Expression::Break(_, val, pair) => Expression::Break(attrs, val, pair),
                _ => unreachable!()
            }
        }
    }
}

pub fn p_expression<'i>(input: &'i str) -> PestResult<Expression<'i>> {
    LookParser::parse(Rule::expression, input).map(|mut pairs| pair_to_expression(pairs.next().unwrap()))
}

#[cfg(test)]
fn assert_sid_expression(t: &Expression, expected: &str) {
    match t {
        &Expression::Id(_, ref id, _) => {
            assert_eq!(id.0[0].as_str(), expected);
        }
        _ => panic!(),
    }
}

#[test]
fn test_expression() {
    assert_sid_expression(&p_expression("abc").unwrap(), "abc");

    let t = p_expression("#[foo]{abc}").unwrap();
    assert_sid_attr(&t.attributes()[0], "foo");
    assert_sid_expression(&t, "abc");

    let t = p_expression("#[foo]#[bar]{abc}").unwrap();
    assert_sid_attr(&t.attributes()[0], "foo");
    assert_sid_attr(&t.attributes()[1], "bar");
    assert_sid_expression(&t, "abc");

    match p_expression("42").unwrap() {
        Expression::Literal(_, Literal::Int(int, _), _) => assert_eq!(int, 42),
        _ => panic!()
    }

    match p_expression("12.34").unwrap() {
        Expression::Literal(_, Literal::Float(float, _), _) => assert_eq!(float, 12.34),
        _ => panic!()
    }

    match p_expression("\"\"").unwrap() {
        Expression::Literal(_, Literal::String(string, _), _) => assert_eq!(string, ""),
        _ => panic!()
    }

    match p_expression("$abc()").unwrap() {
        Expression::MacroInv(attrs, MacroInvocation(id, _, _), _) => {
            assert_eq!(attrs, &[][..]);
            assert_eq!(id.0[0].as_str(), "abc");
        }
        _ => panic!(),
    }

    match p_expression("@abc").unwrap() {
        Expression::Ref(attrs, inner, _) => {
            assert_eq!(attrs, &[][..]);
            assert_sid_expression(inner.as_ref(), "abc");
        }
        _ => panic!()
    }

    match p_expression("~abc").unwrap() {
        Expression::RefMut(attrs, inner, _) => {
            assert_eq!(attrs, &[][..]);
            assert_sid_expression(inner.as_ref(), "abc");
        }
        _ => panic!()
    }

    match p_expression("abc@").unwrap() {
        Expression::Deref(attrs, inner, _) => {
            assert_eq!(attrs, &[][..]);
            assert_sid_expression(inner.as_ref(), "abc");
        }
        _ => panic!()
    }

    match p_expression("abc~").unwrap() {
        Expression::DerefMut(attrs, inner, _) => {
            assert_eq!(attrs, &[][..]);
            assert_sid_expression(inner.as_ref(), "abc");
        }
        _ => panic!()
    }

    match p_expression("[abc]").unwrap() {
        Expression::Array(attrs, inner, _) => {
            assert_eq!(attrs, &[][..]);
            assert_sid_expression(inner.as_ref(), "abc");
        }
        _ => panic!()
    }

    match p_expression("abc[def]").unwrap() {
        Expression::ArrayIndex(attrs, arr, index, _) => {
            assert_eq!(attrs, &[][..]);
            assert_sid_expression(arr.as_ref(), "abc");
            assert_sid_expression(index.as_ref(), "def");
        }
        _ => panic!()
    }

    match p_expression("(abc; 42)").unwrap() {
        Expression::ProductRepeated(attrs, inner, Repetition::Literal(42, _), _) => {
            assert_eq!(attrs, &[][..]);
            assert_sid_expression(inner.as_ref(), "abc");
        }
        _ => panic!()
    }

    match p_expression("()").unwrap() {
        Expression::ProductAnon(attrs, expressions, _) => {
            assert_eq!(attrs, &[][..]);
            assert_eq!(expressions, &[][..]);
        }
        _ => panic!(),
    }

    match p_expression("(abc)").unwrap() {
        Expression::ProductAnon(attrs, expressions, _) => {
            assert_eq!(attrs, &[][..]);
            assert_sid_expression(&expressions[0], "abc");
        }
        _ => panic!(),
    }

    match p_expression("(abc, def)").unwrap() {
        Expression::ProductAnon(attrs, expressions, _) => {
            assert_eq!(attrs, &[][..]);
            assert_sid_expression(&expressions[0], "abc");
            assert_sid_expression(&expressions[1], "def");
        }
        _ => panic!(),
    }

    match p_expression("(abc = def)").unwrap() {
        Expression::ProductNamed(attrs, triples, _) => {
            assert_eq!(attrs, &[][..]);
            assert_eq!(triples[0].0, &[][..]);
            assert_sid(&triples[0].1, "abc");
            assert_sid_expression(&triples[0].2, "def");
        }
        _ => panic!(),
    }

    match p_expression("(abc = def, ghi = jkl)").unwrap() {
        Expression::ProductNamed(attrs, triples, _) => {
            assert_eq!(attrs, &[][..]);
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
        Expression::ProductNamed(attrs, triples, _) => {
            assert_eq!(attrs, &[][..]);
            assert_sid_attr(&triples[0].0[0], "foo");
            assert_sid(&triples[0].1, "abc");
            assert_sid_expression(&triples[0].2, "def");
        }
        _ => panic!(),
    }

    match p_expression("(#[foo]#[bar]{abc = def})").unwrap() {
        Expression::ProductNamed(attrs, triples, _) => {
            assert_eq!(attrs, &[][..]);
            assert_sid_attr(&triples[0].0[0], "foo");
            assert_sid_attr(&triples[0].0[1], "bar");
            assert_sid(&triples[0].1, "abc");
            assert_sid_expression(&triples[0].2, "def");
        }
        _ => panic!(),
    }

    match p_expression("abc.def").unwrap() {
        Expression::ProductAccessNamed(attrs, accessee, field, _) => {
            assert_eq!(attrs, &[][..]);
            assert_sid_expression(&accessee, "abc");
            assert_sid(&field, "def");
        }
        _ => panic!()
    }

    match p_expression("abc.0").unwrap() {
        Expression::ProductAccessAnon(attrs, accessee, Literal::Int(0, _), _) => {
            assert_eq!(attrs, &[][..]);
            assert_sid_expression(&accessee, "abc");
        }
        _ => panic!()
    }

    match p_expression("() -> xyz {}").unwrap() {
        Expression::FunLiteral(attrs, args, return_type, body, _) => {
            assert_eq!(attrs, &[][..]);
            assert_eq!(args, &[][..]);
            assert_sid_type(&return_type, "xyz");
            assert_eq!(body, &[][..]);
        }
        _ => panic!(),
    }

    match p_expression("abc()").unwrap() {
        Expression::FunApplicationAnon(attrs, fun, args, _) => {
            assert_eq!(attrs, &[][..]);
            assert_sid_expression(&fun, "abc");
            assert_eq!(args, &[][..]);
        }
        _ => panic!()
    }

    match p_expression("abc(def = ghi)").unwrap() {
        Expression::FunApplicationNamed(attrs, fun, args, _) => {
            assert_eq!(attrs, &[][..]);
            assert_sid_expression(&fun, "abc");
            assert_eq!(args[0].0, &[][..]);
            assert_sid(&args[0].1, "def");
            assert_sid_expression(&args[0].2, "ghi");
        }
        _ => panic!()
    }

    match p_expression("<abc> => xyz").unwrap() {
        Expression::Generic(attrs, args, exp, _) => {
            assert_eq!(attrs, &[][..]);
            assert_eq!(args[0].0, &[][..]);
            assert_sid(&args[0].1, "abc");
            assert_sid_expression(&exp, "xyz");
        }
        _ => panic!()
    }

    match p_expression("<abc, def> => xyz").unwrap() {
        Expression::Generic(attrs, args, exp, _) => {
            assert_eq!(attrs, &[][..]);
            assert_eq!(args[0].0, &[][..]);
            assert_sid(&args[0].1, "abc");
            assert_eq!(args[1].0, &[][..]);
            assert_sid(&args[1].1, "def");
            assert_sid_expression(&exp, "xyz");
        }
        _ => panic!()
    }

    match p_expression("xyz<abc>").unwrap() {
        Expression::TypeApplicationAnon(attrs, id, args, _) => {
            assert_eq!(attrs, &[][..]);
            assert_sid_id(&id, "xyz");
            assert_sid_type(&args[0], "abc");
        }
        _ => panic!(),
    }

    match p_expression("xyz<abc, def>").unwrap() {
        Expression::TypeApplicationAnon(attrs, id, args, _) => {
            assert_eq!(attrs, &[][..]);
            assert_sid_id(&id, "xyz");
            assert_sid_type(&args[0], "abc");
            assert_sid_type(&args[1], "def");
        }
        _ => panic!(),
    }

    match p_expression("xyz<abc = def>").unwrap() {
        Expression::TypeApplicationNamed(attrs, id, triples, _) => {
            assert_eq!(attrs, &[][..]);
            assert_sid_id(&id, "xyz");
            assert_eq!(triples[0].0, &[][..]);
            assert_sid(&triples[0].1, "abc");
            assert_sid_type(&triples[0].2, "def");
        }
        _ => panic!(),
    }

    match p_expression("xyz<abc = def, ghi = jkl>").unwrap() {
        Expression::TypeApplicationNamed(attrs, id, triples, _) => {
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

    match p_expression("xyz<#[foo]{abc}>").unwrap() {
        Expression::TypeApplicationAnon(attrs, id, args, _) => {
            assert_eq!(attrs, &[][..]);
            assert_sid_id(&id, "xyz");
            assert_sid_type(&args[0], "abc");
        }
        _ => panic!(),
    }

    match p_expression("xyz<#[foo]{abc = def}>").unwrap() {
        Expression::TypeApplicationNamed(attrs, id, triples, _) => {
            assert_eq!(attrs, &[][..]);
            assert_sid_id(&id, "xyz");
            assert_sid_attr(&triples[0].0[0], "foo");
            assert_sid(&triples[0].1, "abc");
            assert_sid_type(&triples[0].2, "def");
        }
        _ => panic!(),
    }

    match p_expression("xyz<#[foo]#[bar]{abc = def}>").unwrap() {
        Expression::TypeApplicationNamed(attrs, id, triples, _) => {
            assert_eq!(attrs, &[][..]);
            assert_sid_id(&id, "xyz");
            assert_sid_attr(&triples[0].0[0], "foo");
            assert_sid_attr(&triples[0].0[1], "bar");
            assert_sid(&triples[0].1, "abc");
            assert_sid_type(&triples[0].2, "def");
        }
        _ => panic!(),
    }

    match p_expression("abc as def").unwrap() {
        Expression::Cast(attrs, exp, the_type, _) => {
            assert_eq!(attrs, &[][..]);
            assert_sid_expression(&exp, "abc");
            assert_sid_type(&the_type, "def");
        }
        _ => panic!()
    }

    match p_expression("abc && def").unwrap() {
        Expression::LAnd(attrs, lhs, rhs, _) => {
            assert_eq!(attrs, &[][..]);
            assert_sid_expression(&lhs, "abc");
            assert_sid_expression(&rhs, "def");
        }
        _ => panic!()
    }

    match p_expression("abc || def").unwrap() {
        Expression::LOr(attrs, lhs, rhs, _) => {
            assert_eq!(attrs, &[][..]);
            assert_sid_expression(&lhs, "abc");
            assert_sid_expression(&rhs, "def");
        }
        _ => panic!()
    }

    match p_expression("abc = def").unwrap() {
        Expression::Assignment(attrs, lhs, rhs, _) => {
            assert_eq!(attrs, &[][..]);
            assert_sid_expression(&lhs, "abc");
            assert_sid_expression(&rhs, "def");
        }
        _ => panic!()
    }

    match p_expression("val _").unwrap() {
        Expression::Val(attrs, Pattern::Blank(_), rhs, _) => {
            assert_eq!(attrs, &[][..]);
            assert_eq!(rhs, None)
        }
        _ => panic!()
    }

    match p_expression("val _ = def").unwrap() {
        Expression::Val(attrs, Pattern::Blank(_), rhs, _) => {
            assert_eq!(attrs, &[][..]);
            assert_sid_expression(rhs.unwrap().as_ref(), "def");
        }
        _ => panic!()
    }

    match p_expression("if a {}").unwrap() {
        Expression::If(attrs, cond, if_block, else_block, _) => {
            assert_eq!(attrs, &[][..]);
            assert_sid_expression(&cond.as_ref(), "a");
            assert_eq!(if_block, &[][..]);
            assert_eq!(else_block, None);
        }
        _ => panic!()
    }

    match p_expression("if a {} else {}").unwrap() {
        Expression::If(attrs, cond, if_block, else_block, _) => {
            assert_eq!(attrs, &[][..]);
            assert_sid_expression(&cond.as_ref(), "a");
            assert_eq!(if_block, &[][..]);
            assert_eq!(else_block.unwrap(), &[][..]);
        }
        _ => panic!()
    }

    match p_expression("if a {} else if b {}").unwrap() {
        Expression::If(attrs, cond, if_block, else_block, _) => {
            assert_eq!(attrs, &[][..]);
            assert_sid_expression(&cond.as_ref(), "a");
            assert_eq!(if_block, &[][..]);
            match else_block.unwrap()[0] {
                Expression::If(ref attrs, ref cond, ref if_block, ref else_block, _) => {
                    assert_eq!(*attrs, &[][..]);
                    assert_sid_expression(cond.as_ref(), "b");
                    assert_eq!(*if_block, &[][..]);
                    assert_eq!(*else_block, None);
                }
                _ => panic!()
            }
        }
        _ => panic!()
    }

    match p_expression("if a {} else if b {} else {}").unwrap() {
        Expression::If(attrs, cond, if_block, else_block, _) => {
            assert_eq!(attrs, &[][..]);
            assert_sid_expression(&cond.as_ref(), "a");
            assert_eq!(if_block, &[][..]);
            match else_block.unwrap()[0] {
                Expression::If(ref attrs, ref cond, ref if_block, ref mut else_block, _) => {
                    assert_eq!(*attrs, &[][..]);
                    assert_sid_expression(cond.as_ref(), "b");
                    assert_eq!(*if_block, &[][..]);
                    assert_eq!(else_block.take().unwrap(), &[][..]);
                }
                _ => panic!()
            }
        }
        _ => panic!()
    }

    match p_expression("case abc {}").unwrap() {
        Expression::Case(_, matcher, branches, _) => {
            assert_sid_expression(&matcher, "abc");
            assert_eq!(branches.len(), 0);
        }
        _ => panic!()
    }

    match p_expression("case abc {_{}_{}}").unwrap() {
        Expression::Case(_, matcher, branches, _) => {
            assert_sid_expression(&matcher, "abc");
            assert_eq!(branches.len(), 2);
        }
        _ => panic!()
    }

    match p_expression("while abc {}").unwrap() {
        Expression::While(_, cond, block, _) => {
            assert_sid_expression(&cond, "abc");
            assert_eq!(block.len(), 0);
        }
        _ => panic!()
    }

    match p_expression("loop abc {}").unwrap() {
        Expression::Loop(_, matcher, branches, _) => {
            assert_sid_expression(&matcher, "abc");
            assert_eq!(branches.len(), 0);
        }
        _ => panic!()
    }

    match p_expression("loop abc {_{}_{}}").unwrap() {
        Expression::Loop(_, matcher, branches, _) => {
            assert_sid_expression(&matcher, "abc");
            assert_eq!(branches.len(), 2);
        }
        _ => panic!()
    }

    match p_expression("return").unwrap() {
        Expression::Return(_, val, _) => {
            assert_eq!(val, None);
        }
        _ => panic!()
    }

    match p_expression("return abc").unwrap() {
        Expression::Return(_, val, _) => {
            assert_sid_expression(&val.unwrap(), "abc");
        }
        _ => panic!()
    }

    match p_expression("break").unwrap() {
        Expression::Break(_, val, _) => {
            assert_eq!(val, None);
        }
        _ => panic!()
    }

    match p_expression("break abc").unwrap() {
        Expression::Break(_, val, _) => {
            assert_sid_expression(&val.unwrap(), "abc");
        }
        _ => panic!()
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum UsePrefix<'i> {
    Mod(Pair<'i, Rule>),
    Dep(Pair<'i, Rule>),
    Magic(Pair<'i, Rule>),
    None
}

fn pair_to_use_prefix<'i>(pair: Pair<'i, Rule>) -> UsePrefix<'i> {
    debug_assert!(pair.as_rule() == Rule::use_prefix);
    let p = pair.clone().into_inner().next();

    match p {
        None => UsePrefix::None,
        Some(p) => match p.as_rule() {
            Rule::_mod => UsePrefix::Mod(pair),
            Rule::_dep => UsePrefix::Dep(pair),
            Rule::_magic => UsePrefix::Magic(pair),
            _ => unreachable!(),
        }
    }
}

pub fn p_use_prefix<'i>(input: &'i str) -> PestResult<UsePrefix<'i>> {
    LookParser::parse(Rule::use_prefix, input).map(|mut pairs| pair_to_use_prefix(pairs.next().unwrap()))
}

#[test]
fn test_use_prefix() {
    match p_use_prefix("mod::").unwrap() {
        UsePrefix::Mod(_) => {}
        _ => panic!()
    }

    match p_use_prefix("dep::").unwrap() {
        UsePrefix::Dep(_) => {}
        _ => panic!()
    }

    match p_use_prefix("magic::").unwrap() {
        UsePrefix::Magic(_) => {}
        _ => panic!()
    }

    match p_use_prefix("").unwrap() {
        UsePrefix::None => {}
        _ => panic!()
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum UseTree<'i> {
    IdLeaf(SimpleIdentifier<'i>, Pair<'i, Rule>),
    SelfLeaf(Pair<'i, Rule>),
    IdRenamedLeaf(SimpleIdentifier<'i>, SimpleIdentifier<'i>, Pair<'i, Rule>),
    SelfRenamedLeaf(SimpleIdentifier<'i>, Pair<'i, Rule>),
    IdBranch(SimpleIdentifier<'i>, Vec<(Vec<Attribute<'i>>, UseTree<'i>)>, Pair<'i, Rule>),
    SuperBranch(Vec<(Vec<Attribute<'i>>, UseTree<'i>)>, Pair<'i, Rule>),
}

fn pair_to_use_branch<'i>(p: Pair<'i, Rule>) -> Vec<(Vec<Attribute<'i>>, UseTree<'i>)> {
    debug_assert!(p.as_rule() == Rule::use_branch);

    let mut branches = vec![];

    for pair in p.into_inner() {
        match pair.as_rule() {
            Rule::use_tree => {
                branches.push((vec![], pair_to_use_tree(pair)));
            }
            Rule::attributed_use_tree => {
                let mut attrs = vec![];
                let mut tree = None;
                for inner_pair in pair.into_inner() {
                    match inner_pair.as_rule() {
                        Rule::attribute => attrs.push(pair_to_attribute(inner_pair)),
                        Rule::use_tree => tree = Some(pair_to_use_tree(inner_pair)),
                        _ => unreachable!()
                    }
                }
                branches.push((attrs, tree.unwrap()));
            }
            _ => unreachable!()
        }
    }

    return branches;
}

fn pair_to_use_tree<'i>(p: Pair<'i, Rule>) -> UseTree<'i> {
    debug_assert!(p.as_rule() == Rule::use_tree);
    let mut pairs = p.clone().into_inner().peekable();

    let pair = pairs.next().unwrap();
    match pair.as_rule() {
        Rule::_self => {
            let is_rename = pairs.peek().is_some();
            if is_rename {
                assert!(pairs.next().unwrap().as_rule() == Rule::_as);
                UseTree::SelfRenamedLeaf(pair_to_simple_identifier(pairs.next().unwrap()), p)
            } else {
                UseTree::SelfLeaf(p)
            }
        },
        Rule::sid => {
            let sid = pair_to_simple_identifier(pair);
            match pairs.next() {
                None => UseTree::IdLeaf(sid, p),
                Some(pair) => {
                    match pair.as_rule() {
                        Rule::scope => UseTree::IdBranch(sid, pair_to_use_branch(pairs.next().unwrap()), p),
                        Rule::_as => UseTree::IdRenamedLeaf(sid, pair_to_simple_identifier(pairs.next().unwrap()), p),
                        _ => unreachable!()
                    }
                }
            }
        }
        Rule::_super => {
            debug_assert!(pairs.next().unwrap().as_rule() == Rule::scope);
            UseTree::SuperBranch(pair_to_use_branch(pairs.next().unwrap()), p)
        }
        _ => unreachable!(),
    }
}

pub fn p_use_tree<'i>(input: &'i str) -> PestResult<UseTree<'i>> {
    LookParser::parse(Rule::use_tree, input).map(|mut pairs| pair_to_use_tree(pairs.next().unwrap()))
}

#[test]
fn test_use_tree() {
    match p_use_tree("abc").unwrap() {
        UseTree::IdLeaf(sid, _) => assert_sid(&sid, "abc"),
        _ => panic!()
    }

    match p_use_tree("super::{foo::bar, self}").unwrap() {
        UseTree::SuperBranch(mut branches, _) => {
            match branches.pop().unwrap() {
                (attrs, UseTree::SelfLeaf(_)) => {
                    assert_eq!(attrs.len(), 0);
                }
                _ => panic!()
            }

            match branches.pop().unwrap() {
                (attrs, UseTree::IdBranch(sid, mut branches, _)) => {
                    assert_eq!(attrs.len(), 0);
                    assert_sid(&sid, "foo");
                    match branches.pop().unwrap() {
                        (attrs, UseTree::IdLeaf(sid, _)) => {
                            assert_eq!(attrs.len(), 0);
                            assert_sid(&sid, "bar");
                        }
                        _ => panic!()
                    }
                }
                _ => panic!()
            }
        }
        _ => panic!()
    }

    match p_use_tree("abc::{#[foo]#[bar]{def}}").unwrap() {
        UseTree::IdBranch(sid, mut branches, _) => {
            assert_sid(&sid, "abc");
            match branches.pop().unwrap() {
                (attrs, UseTree::IdLeaf(sid, _)) => {
                    assert_sid(&sid, "def");
                    assert_eq!(attrs.len(), 2)
                }
                _ => panic!(),
            }
        }
        _ => panic!()
    }

    match p_use_tree("super::{foo as bar, self as baz}").unwrap() {
        UseTree::SuperBranch(mut branches, _) => {
            match branches.pop().unwrap() {
                (attrs, UseTree::SelfRenamedLeaf(sid, _)) => {
                    assert_eq!(attrs.len(), 0);
                    assert_sid(&sid, "baz");
                }
                _ => panic!()
            }

            match branches.pop().unwrap() {
                (attrs, UseTree::IdRenamedLeaf(sid, new_name, _)) => {
                    assert_eq!(attrs.len(), 0);
                    assert_sid(&sid, "foo");
                    assert_sid(&new_name, "bar");
                }
                _ => panic!()
            }
        }
        _ => panic!()
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum FfiLanguage {
    C
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum FfiItem<'i> {
    Type(bool, SimpleIdentifier<'i>, Pair<'i, Rule>),
    Val(bool, SimpleIdentifier<'i>, Type<'i>, Pair<'i, Rule>),
}

fn pair_to_ffi_item<'i>(p: Pair<'i, Rule>) -> FfiItem<'i> {
    debug_assert!(p.as_rule() == Rule::ffi_item);
    let pair = p.clone().into_inner().next().unwrap();

    match pair.as_rule() {
        Rule::ffi_type => {
            let mut pairs = pair.into_inner().peekable();
            let public = pairs.peek().unwrap().as_rule() == Rule::_pub;

            if public {
                pairs.next();
            }

            assert!(pairs.next().unwrap().as_rule() == Rule::_type_kw);
            return FfiItem::Type(public, pair_to_simple_identifier(pairs.next().unwrap()), p);
        }
        Rule::ffi_val => {
            let mut pairs = pair.into_inner().peekable();
            let public = pairs.peek().unwrap().as_rule() == Rule::_pub;

            if public {
                pairs.next();
            }

            assert!(pairs.next().unwrap().as_rule() == Rule::_val);
            let sid = pair_to_simple_identifier(pairs.next().unwrap());
            return FfiItem::Val(public, sid, pair_to_type(pairs.next().unwrap()), p);
        }
        _ => unreachable!()
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Item<'i> {
    Use(bool, UsePrefix<'i>, UseTree<'i>, Pair<'i, Rule>),
    Type(bool, SimpleIdentifier<'i>, TypeDef<'i>, Pair<'i, Rule>),
    Val(bool, Pattern<'i>, Expression<'i>, Pair<'i, Rule>),
    FfiBlock(FfiLanguage, Vec<(Vec<Attribute<'i>>, FfiItem<'i>)>, Pair<'i, Rule>),
}

fn pair_to_use_item<'i>(p: Pair<'i, Rule>) -> Item<'i> {
    debug_assert!(p.as_rule() == Rule::use_item);
    let mut pairs = p.clone().into_inner().peekable();
    let public = pairs.peek().unwrap().as_rule() == Rule::_pub;

    if public {
        pairs.next();
    }

    assert!(pairs.next().unwrap().as_rule() == Rule::_use);

    let prefix = pair_to_use_prefix(pairs.next().unwrap());
    let tree = pair_to_use_tree(pairs.next().unwrap());

    Item::Use(public, prefix, tree, p)
}

fn pair_to_type_item<'i>(p: Pair<'i, Rule>) -> Item<'i> {
    debug_assert!(p.as_rule() == Rule::type_item);
    let mut pairs = p.clone().into_inner().peekable();
    let public = pairs.peek().unwrap().as_rule() == Rule::_pub;

    if public {
        pairs.next();
    }

    assert!(pairs.next().unwrap().as_rule() == Rule::_type_kw);

    let sid = pair_to_simple_identifier(pairs.next().unwrap());
    let type_def = pair_to_type_def(pairs.next().unwrap());

    Item::Type(public, sid, type_def, p)
}

fn pair_to_val_item<'i>(p: Pair<'i, Rule>) -> Item<'i> {
    debug_assert!(p.as_rule() == Rule::val_item);
    let mut pairs = p.clone().into_inner().peekable();
    let public = pairs.peek().unwrap().as_rule() == Rule::_pub;

    if public {
        pairs.next();
    }

    assert!(pairs.next().unwrap().as_rule() == Rule::_val);

    let pattern = pair_to_pattern(pairs.next().unwrap());
    let val = pair_to_expression(pairs.next().unwrap());

    Item::Val(public, pattern, val, p)
}

fn pair_to_ffi_block<'i>(p: Pair<'i, Rule>) -> Item<'i> {
    debug_assert!(p.as_rule() == Rule::ffi_block);
    let mut pairs = p.clone().into_inner();

    assert!(pairs.next().unwrap().as_rule() == Rule::_ffi);
    assert!(pairs.next().unwrap().as_rule() == Rule::ffi_language);

    let mut block_items = vec![];
    let mut attrs = vec![];

    for pair in pairs {
        match pair.as_rule() {
            Rule::attribute => {
                attrs.push(pair_to_attribute(pair));
            }
            Rule::ffi_item => {
                block_items.push((attrs.clone(), pair_to_ffi_item(pair)));
                attrs = vec![];
            }
            _ => unreachable!()
        }
    }

    Item::FfiBlock(FfiLanguage::C, block_items, p)
}

fn pair_to_item<'i>(p: Pair<'i, Rule>) -> Item<'i> {
    debug_assert!(p.as_rule() == Rule::item);
    let pair = p.into_inner().next().unwrap();

    match pair.as_rule() {
        Rule::use_item => pair_to_use_item(pair),
        Rule::type_item => pair_to_type_item(pair),
        Rule::val_item => pair_to_val_item(pair),
        Rule::ffi_block => pair_to_ffi_block(pair),
        _ => unreachable!()
    }
}

pub fn p_item<'i>(input: &'i str) -> PestResult<Item<'i>> {
    LookParser::parse(Rule::item, input).map(|mut pairs| pair_to_item(pairs.next().unwrap()))
}

#[test]
fn test_item() {
    match p_item("use foo").unwrap() {
        Item::Use(false, UsePrefix::None, UseTree::IdLeaf(sid, _), _) => {
            assert_sid(&sid, "foo");
        }
        _ => panic!()
    }

    match p_item("pub use self").unwrap() {
        Item::Use(true, UsePrefix::None, UseTree::SelfLeaf(_), _) => {}
        _ => panic!()
    }

    match p_item("type foo = bar").unwrap() {
        Item::Type(false, sid, inner, _) => {
            assert_sid(&sid, "foo");
            assert_sid_type_def(&inner, "bar");
        }
        _ => panic!()
    }

    match p_item("pub type foo = bar").unwrap() {
        Item::Type(true, sid, inner, _) => {
            assert_sid(&sid, "foo");
            assert_sid_type_def(&inner, "bar");
        }
        _ => panic!()
    }

    match p_item("val _ = bar").unwrap() {
        Item::Val(false, Pattern::Blank(_), inner, _) => {
            assert_sid_expression(&inner, "bar");
        }
        _ => panic!()
    }

    match p_item("pub val _ = bar").unwrap() {
        Item::Val(true, Pattern::Blank(_), inner, _) => {
            assert_sid_expression(&inner, "bar");
        }
        _ => panic!()
    }

    match p_item("ffi C {pub type abc val def: ghi}").unwrap() {
        Item::FfiBlock(FfiLanguage::C, mut items, _) => {
            match items.pop().unwrap() {
                (attrs, FfiItem::Val(false, sid, the_type, _)) => {
                    assert_eq!(attrs.len(), 0);
                    assert_sid(&sid, "def");
                    assert_sid_type(&the_type, "ghi");
                }
                _ => panic!()
            }

            match items.pop().unwrap() {
                (attrs, FfiItem::Type(true, sid, _)) => {
                    assert_eq!(attrs.len(), 0);
                    assert_sid(&sid, "abc");
                }
                _ => panic!()
            }
        }
        _ => panic!()
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct File<'i>(pub Vec<(Vec<Attribute<'i>>, Item<'i>)>);

fn pair_to_file<'i>(p: Pair<'i, Rule>) -> File<'i> {
    debug_assert!(p.as_rule() == Rule::file);

    let mut items = vec![];

    for pair in p.clone().into_inner() {
        debug_assert!(pair.as_rule() == Rule::file_item);
        let mut attrs = vec![];

        for pair in pair.into_inner() {
            match pair.as_rule() {
                Rule::attribute => {
                    attrs.push(pair_to_attribute(pair));
                }
                Rule::item => {
                    items.push((attrs.clone(), pair_to_item(pair)));
                }
                _ => unreachable!()
            }
        }
    }

    File(items)
}

pub fn p_file<'i>(input: &'i str) -> PestResult<File<'i>> {
    LookParser::parse(Rule::file, input).map(|mut pairs| pair_to_file(pairs.next().unwrap()))
}

#[test]
fn test_file() {
    let File(mut items) = p_file("val _ = foo #[foo] { type bar = baz }").unwrap();

    match items.pop().unwrap() {
        (attrs, Item::Type(false, sid, type_def, _)) => {
            assert_eq!(attrs.len(), 1);
            assert_sid(&sid, "bar");
            assert_sid_type_def(&type_def, "baz");
        }
        _ => panic!()
    }

    match items.pop().unwrap() {
        (attrs, Item::Val(false, Pattern::Blank(_), inner, _)) => {
            assert_eq!(attrs.len(), 0);
            assert_sid_expression(&inner, "foo");
        }
        _ => panic!()
    }
}

// Well-known types: Void, Bool, U8, I8, U16, I16, U32, I32, U64, I64, USize, ISize, F32, F64
//
// List of magic:
//
// - `sizeof` macro
// - modules for functions for the well-known types (e.g. magic::i32::add, magic::bool::not)
// And some magic that can be added later as needed
// - `alignof` macro (can be added later)
// - stringify macro for features (also parse_intify, parse_floatify and a bool macro)
//
// List of attributes:
//
// - conditional compilation (`cond`)
// - repr (C)
// - test
