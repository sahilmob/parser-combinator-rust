type ParseResult<'a, Output> = Result<(&'a str, Output), ParserError<'a>>;
type ParserError<'a> = (&'a str, String);

pub trait Parser<'a, Output> {
    fn parse(&self, source: &'a str) -> ParseResult<'a, Output>;
}

impl<'a, F, Output> Parser<'a, Output> for F
where
    F: Fn(&'a str) -> ParseResult<'a, Output>,
{
    fn parse(&self, source: &'a str) -> ParseResult<'a, Output> {
        self(source)
    }
}

pub fn map<'a, P, RIN, F, ROUT>(parser: P, map_fn: F) -> impl Parser<'a, ROUT>
where
    P: Parser<'a, RIN>,
    F: Fn(RIN) -> ROUT,
{
    move |source| {
        parser
            .parse(source)
            .map(|(remainder, result)| (remainder, map_fn(result)))
    }
}

pub fn optional<'a, P, R>(parser: P) -> impl Parser<'a, Option<R>>
where
    P: Parser<'a, R>,
{
    let mapped = map(parser, move |r| Some(r));
    move |source| mapped.parse(source).or(Ok((source, None)))
}

pub fn left<'a, P1, P2, R1, R2>(parser1: P1, parser2: P2) -> impl Parser<'a, R1>
where
    P1: Parser<'a, R1>,
    P2: Parser<'a, R2>,
{
    move |source| {
        parser1.parse(source).and_then(|(remainder, r1)| {
            parser2
                .parse(remainder)
                .map(|(final_remainder, _r2)| (final_remainder, r1))
        })
    }
}

pub fn right<'a, P1, P2, R1, R2>(parser1: P1, parser2: P2) -> impl Parser<'a, R2>
where
    P1: Parser<'a, R1>,
    P2: Parser<'a, R2>,
{
    move |source| {
        parser1
            .parse(source)
            .and_then(|(remainder, _r1)| parser2.parse(remainder))
    }
}

pub fn pair<'a, P1, P2, R1, R2>(parser1: P1, parser2: P2) -> impl Parser<'a, (R1, R2)>
where
    P1: Parser<'a, R1>,
    P2: Parser<'a, R2>,
{
    move |source| {
        parser1.parse(source).and_then(|(remainder, r1)| {
            parser2
                .parse(remainder)
                .map(|(final_remainder, r2)| (final_remainder, (r1, r2)))
        })
    }
}

pub fn whitespace(source: &'_ str) -> ParseResult<'_, ()> {
    if source.is_empty() {
        return Err((source, "Unexpected EOF. Expected whitespace".into()));
    }

    let mut chars = source.chars();
    let mut end_index = 0;

    while chars.next().is_some_and(|c| c.is_whitespace()) {
        end_index += 1;
    }

    Ok((&source[end_index..], ()))
}

pub fn integer(source: &'_ str) -> ParseResult<'_, i64> {
    let mut chars = source.chars();
    let mut end_index = 0;

    if source.starts_with("-") {
        chars.next();
        end_index += 1;
    }

    while chars.next().is_some_and(|c| c.is_numeric()) {
        end_index += 1;
    }

    let parse_result = source[..end_index]
        .parse::<i64>()
        .map_err(|_| (source, "Expected integer".into()))?;

    Ok((&source[end_index..], parse_result))
}

pub fn parser_literal<'a>(target: &'a str) -> impl Parser<'a, ()> {
    move |source: &'a str| {
        source
            .strip_prefix(target)
            .ok_or((source, format!("Expected literal '{}'", target)))
            .map(|remainder| (remainder, ()))
    }
}

fn valid_identifier(ch: char) -> bool {
    ch.is_alphabetic() || ch.is_numeric() || ch == '_'
}

pub fn identifier(source: &'_ str) -> ParseResult<'_, &'_ str> {
    let mut chars = source.chars();
    let first = chars.next().ok_or((source, "Unexpected EOF".into()))?;

    if !first.is_alphabetic() {
        return Err((source, "Identifiers must begin with a letter".into()));
    }

    let start_index = 0;
    let mut end_index = 1;

    let mut next = chars.next();

    while next.is_some_and(valid_identifier) {
        next = chars.next();
        end_index += 1;
    }

    let id = &source[start_index..end_index];

    Ok((&source[end_index..], id))
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn parse_identifier() {
        let code = "variable = 3";
        let (remainder, identifier) = identifier(code).expect("Parsing failed");
        assert_eq!(identifier, "variable");
        assert_eq!(remainder, " = 3");
    }

    #[test]
    #[should_panic]
    fn parse_identifier_fails() {
        let code = "3variable = 3";
        let _ = identifier(code).unwrap();
    }

    #[test]
    fn parse_identifier_single() {
        let code = "v    = 3";
        let (remainder, identifier) = identifier(code).expect("Parsing failed");
        assert_eq!(identifier, "v");
        assert_eq!(remainder, "    = 3");
    }

    #[test]
    fn parse_literal() {
        let code = "= 3";
        let (remainder, value) = parser_literal("=").parse(code).expect("Parsing failed");
        assert_eq!(value, ());
        assert_eq!(remainder, " 3");
    }

    #[test]
    fn parse_long_literal() {
        let code = "= 3";
        let (remainder, value) = parser_literal("= 3").parse(code).expect("Parsing failed");
        assert_eq!(value, ());
        assert!(remainder.is_empty());
    }

    #[test]
    fn parse_integer() {
        let code = "3";
        let (remainder, value) = integer(code).expect("Parsing failed");
        assert_eq!(value, 3);
        assert!(remainder.is_empty());
    }

    #[test]
    fn parse_long_integer() {
        let code = "32232";
        let (remainder, value) = integer(code).expect("Parsing failed");
        assert_eq!(value, 32232);
        assert!(remainder.is_empty());
    }

    #[test]
    fn parse_negative_integer() {
        let code = "-3";
        let (remainder, value) = integer(code).expect("Parsing failed");
        assert_eq!(value, -3);
        assert!(remainder.is_empty());
    }

    #[test]
    fn parse_whitespace() {
        let code = "   -3";
        let (remainder, _value) = whitespace(code).expect("Parsing failed");
        assert_eq!(remainder, "-3");
    }

    #[test]
    fn parse_identifier_whitespace_pair() {
        let code = "foo   =-3";
        let pair_parser = pair(identifier, whitespace);
        let (remainder, (id, _)) = pair_parser.parse(code).expect("Parsing failed");
        assert_eq!(remainder, "=-3");
        assert_eq!(id, "foo");
    }

    #[test]
    #[should_panic]
    fn fail_on_empty_integer() {
        integer("").unwrap();
    }

    #[test]
    #[should_panic]
    fn fail_on_empty_whitespace() {
        whitespace("").unwrap();
    }

    #[test]
    fn parse_identifier_whitespace_left() {
        let code = "foo   =-3";
        let pair_parser = left(identifier, whitespace);
        let (remainder, id) = pair_parser.parse(code).expect("Parsing failed");
        assert_eq!(remainder, "=-3");
        assert_eq!(id, "foo");
    }

    #[test]
    #[should_panic]
    fn parse_identifier_whitespace_left_but_no_whitespace() {
        let code = "foo";
        let pair_parser = left(identifier, whitespace);
        pair_parser.parse(code).unwrap();
    }

    #[test]
    fn parse_identifier_whitespace_left_but_no_whitespace_optional() {
        let code = "foo";
        let pair_parser = left(identifier, optional(whitespace));
        let (remainder, id) = pair_parser.parse(code).expect("Parsing failed");
        assert_eq!(remainder, "");
        assert_eq!(id, "foo");
    }

    #[test]
    fn parse_identifier_whitespace_right() {
        let code = "foo   =-3";
        let pair_parser = right(identifier, whitespace);
        let (remainder, value) = pair_parser.parse(code).expect("Parsing failed");
        assert_eq!(remainder, "=-3");
        assert_eq!(value, ());
    }
}
