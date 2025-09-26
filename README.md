![CI](https://github.com/sahilmob/parser-combinator-rust/actions/workflows/ci.yml/badge.svg)

#

### A Rust-based implementation for Parser combinators.

It supports the following combinators:

```
identifier
literal
integer
whitespace
pair
right
left
optional
map
between
either
many
```

Example of parsing [Redis serialization protocol message (RSEP)](https://redis.io/docs/latest/develop/reference/protocol-spec/):

```rust
type FirstByteResult<'a> = Option<(&'a str, &'a str)>;
type ParseCommandResult<'a> = Result<(&'a str, ParsedSegment), (&'a str, String)>;

#[derive(PartialEq, Debug, Clone)]
pub enum ParsedSegment {
    SimpleString(SimpleString),
    Integer(Integer),
    Float(Float),
    Array(Array),
}

const ARRAY_FB: &str = "*";
const FB: [&str; 1] = [
    ARRAY_FB,
];

fn parse_first_byte(source: &str) -> FirstByteResult<'_> {
    let mut result = None;
    for s in FB {
        let parser = parser_literal(s).parse(source);
        if let Ok((rest, _)) = parser {
            result = Some((rest, s));
            break;
        }
    }

    result
}


pub fn parse(source: &'_ str) -> ParseCommandResult<'_> {
    let mut result: ParseCommandResult = Err((source, "Parsing failed".into()));
    if let Some((rest, first_byte)) = parse_first_byte(source) {
        match first_byte {
            ARRAY_FB => {
                let mut array: Vec<ParsedSegment> = Vec::new();
                let mut count = 0;
                let (mut re, length) = left(integer, parser_literal("\r\n")).parse(rest)?;
                while count < length {
                    let (rest, _) = pair(parser_literal("$"), integer).parse(re)?;
                    let (rest, e) = right(
                        parser_literal("\r\n"),
                        either(identifier, either(float, integer)),
                    )
                    .parse(rest)?;
                    if count + 1 < length {
                        let (r, _) = parser_literal("\r\n").parse(rest)?;
                        re = r;
                    } else {
                        re = rest;
                    }

                    let val = match e {
                        Either::Left(l) => ParsedSegment::SimpleString(SimpleString {
                            value: l.to_string(),
                        }),
                        Either::Right(r) => match r {
                            Either::Left(f) => ParsedSegment::Float(Float { value: f }),
                            Either::Right(i) => ParsedSegment::Integer(Integer { value: i }),
                        },
                    };

                    array.push(val);

                    count += 1;
                }

                result = Ok((re, ParsedSegment::Array(Array { value: array })))
            }
            _ => {
                todo!("Handle other first_byte possibilities");
            }
        }
    }

    let (rest, result) = result.unwrap();

    let (rest, _) = parser_literal("\r\n").parse(rest)?;

    Ok((rest, result))
}
```

Original source: This was implemented as a code-along exercise with [this parser combinators series](https://www.youtube.com/watch?v=7PPDHskv0Mw).
