// TODO: resolver depois
#![allow(deprecated)]
use nom::{
    bytes::complete::tag,
    character::complete::{alpha1, char, digit1, multispace0, multispace1},
    combinator::{map, map_res, recognize},
    multi::many0,
    sequence::{delimited, pair, preceded, separated_pair, terminated, tuple},
    IResult, Parser,
};
use std::str::FromStr;

use super::Automata;

fn identifier(input: &str) -> IResult<&str, &str> {
    recognize(pair(
        alpha1,
        nom::bytes::complete::take_while(|c: char| c.is_ascii_alphanumeric() || c == '_'),
    ))
    .parse(input)
}

fn number(input: &str) -> IResult<&str, u32> {
    map_res(digit1, FromStr::from_str).parse(input)
}

fn initial_state(input: &str) -> IResult<&str, &str> {
    preceded(
        terminated(tag("init"), multispace1),
        terminated(recognize(identifier), char(';')),
    )
    .parse(input)
}

fn accepting_state(input: &str) -> IResult<&str, &str> {
    preceded(
        terminated(tag("accepting"), multispace1),
        terminated(recognize(identifier), char(';')),
    )
    .parse(input)
}

fn char_range(input: &str) -> IResult<&str, (u32, u32)> {
    delimited(
        char('['),
        separated_pair(
            preceded(multispace0, number),
            preceded(multispace0, char(',')),
            preceded(multispace0, number),
        ),
        char(']'),
    )
    .parse(input)
}

fn transition(input: &str) -> IResult<&str, (&str, &str, (u32, u32))> {
    map(
        tuple((
            terminated(identifier, preceded(multispace0, tag("->"))),
            preceded(multispace0, identifier),
            preceded(multispace0, terminated(char_range, char(';'))),
        )),
        |(from, to, range)| (from, to, range),
    )
    .parse(input)
}

pub fn parse_automata(input: &str) -> IResult<&str, Automata> {
    map(
        terminated(
            tuple((
                preceded(
                    terminated(tag("automaton"), multispace1),
                    terminated(identifier, multispace0),
                ),
                delimited(
                    char('{'),
                    tuple((
                        preceded(multispace0, initial_state),
                        many0(preceded(multispace0, transition)),
                        many0(preceded(multispace0, accepting_state)),
                    )),
                    preceded(multispace0, char('}')),
                ),
            )),
            char(';'),
        ),
        |(name, (initial_state, transitions, accepting_states))| {
            Automata::new(
                name.to_owned(),
                initial_state,
                transitions,
                accepting_states,
            )
        },
    )
    .parse(input)
}
