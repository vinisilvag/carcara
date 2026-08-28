use ansi_term::{Color, Style};
use carcara::parser::Position;
use std::{fmt, io, path::PathBuf};

#[derive(Debug)]
pub enum CliError {
    CarcaraError(carcara::Error),
    CantInferProblemFile(PathBuf),
    InvalidSliceId(String),
    BothFilesStdin,
}

pub type CliResult<T> = Result<T, CliError>;

fn pretty_error(
    f: &mut fmt::Formatter,
    error: impl fmt::Display,
    file: &str,
    pos: Option<Position>,
    more_info: Option<String>,
) -> fmt::Result {
    writeln!(f, "{}", error)?;
    write!(
        f,
        "  {} in file {}",
        Color::Blue.paint("-->"),
        Color::Blue.underline().paint(file),
    )?;
    if let Some((line, column)) = pos {
        writeln!(f, ":{}:{}", line, column)?;
    } else {
        writeln!(f)?;
    }
    if let Some(info) = more_info {
        writeln!(f, "  {} {}", Style::new().bold().paint("note:"), info)?;
    }
    Ok(())
}

impl From<io::Error> for CliError {
    fn from(e: io::Error) -> Self {
        Self::CarcaraError(carcara::Error::Io(e))
    }
}

impl From<carcara::Error> for CliError {
    fn from(e: carcara::Error) -> Self {
        Self::CarcaraError(e)
    }
}

impl fmt::Display for CliError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            CliError::CarcaraError(carcara::Error::Parser(e, pos, file)) => {
                pretty_error(f, e, file, Some(*pos), None)
            }
            CliError::CarcaraError(e) => write!(f, "{}", e), // TODO: prettier errors for other types
            CliError::CantInferProblemFile(p) => {
                write!(f, "can't infer problem file: {}", p.display())
            }
            CliError::BothFilesStdin => write!(f, "problem and proof files can't both be `-`"),
            CliError::InvalidSliceId(id) => write!(f, "invalid id for slice: {}", id),
        }
    }
}
