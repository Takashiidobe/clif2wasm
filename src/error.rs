use std::fmt::{self, Display};

use miette::{Diagnostic, LabeledSpan, NamedSource, SourceCode, SourceSpan};
use thiserror::Error as ThisError;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[repr(u16)]
pub enum ErrorCode {
    InternalInvariant = 1000,
    UnsupportedOpcode = 2000,
    UnsupportedType = 2001,
    UnsupportedRepresentation = 2002,
    General = 3000,
}

impl ErrorCode {
    pub const fn number(self) -> u16 {
        self as u16
    }
}

impl Display for ErrorCode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "CLIF2WASM-E{:04}", self.number())
    }
}

#[derive(Debug, ThisError)]
pub enum Error {
    #[error("internal translation error [{code}]: {message}")]
    Internal {
        code: ErrorCode,
        message: String,
        source_code: Option<NamedSource<String>>,
        span: Option<SourceSpan>,
        #[source]
        cause: Option<Box<dyn std::error::Error + Send + Sync>>,
    },
    #[error("unsupported CLIF [{code}]: {message}")]
    Unsupported {
        code: ErrorCode,
        message: String,
        source_code: Option<NamedSource<String>>,
        span: Option<SourceSpan>,
        #[source]
        cause: Option<Box<dyn std::error::Error + Send + Sync>>,
    },
    #[error("{message} [{code}]")]
    Error {
        code: ErrorCode,
        message: String,
        source_code: Option<NamedSource<String>>,
        span: Option<SourceSpan>,
        #[source]
        cause: Option<Box<dyn std::error::Error + Send + Sync>>,
    },
}

pub type Result<T> = std::result::Result<T, Error>;

impl Error {
    pub fn internal(message: impl Into<String>) -> Self {
        Self::internal_with_code(ErrorCode::InternalInvariant, message)
    }

    pub fn internal_with_code(code: ErrorCode, message: impl Into<String>) -> Self {
        Self::Internal {
            code,
            message: message.into(),
            source_code: None,
            span: None,
            cause: None,
        }
    }

    pub fn unsupported(message: impl Into<String>) -> Self {
        Self::unsupported_with_code(ErrorCode::UnsupportedOpcode, message)
    }

    pub fn unsupported_with_code(code: ErrorCode, message: impl Into<String>) -> Self {
        Self::Unsupported {
            code,
            message: message.into(),
            source_code: None,
            span: None,
            cause: None,
        }
    }

    pub fn general(message: impl Into<String>) -> Self {
        Self::Error {
            code: ErrorCode::General,
            message: message.into(),
            source_code: None,
            span: None,
            cause: None,
        }
    }

    pub fn at_instruction(self, function: &str, instruction: &str) -> Self {
        let rendered = format!("{function}:\n  {instruction}");
        let span = Some((rendered.len() - instruction.len(), instruction.len()).into());
        let source_code = Some(NamedSource::new(function, rendered));
        match self {
            Self::Internal {
                code,
                message,
                cause,
                ..
            } => Self::Internal {
                code,
                message,
                cause,
                source_code,
                span,
            },
            Self::Unsupported {
                code,
                message,
                cause,
                ..
            } => Self::Unsupported {
                code,
                message,
                cause,
                source_code,
                span,
            },
            Self::Error {
                code,
                message,
                cause,
                ..
            } => Self::Error {
                code,
                message,
                cause,
                source_code,
                span,
            },
        }
    }

    fn with_source(self, cause: Box<dyn std::error::Error + Send + Sync>) -> Self {
        match self {
            Self::Internal {
                code,
                message,
                source_code,
                span,
                ..
            } => Self::Internal {
                code,
                message,
                source_code,
                span,
                cause: Some(cause),
            },
            Self::Unsupported {
                code,
                message,
                source_code,
                span,
                ..
            } => Self::Unsupported {
                code,
                message,
                source_code,
                span,
                cause: Some(cause),
            },
            Self::Error {
                code,
                message,
                source_code,
                span,
                ..
            } => Self::Error {
                code,
                message,
                source_code,
                span,
                cause: Some(cause),
            },
        }
    }

    fn prepend_context(self, context: &str) -> Self {
        match self {
            Self::Internal {
                code,
                message,
                source_code,
                span,
                cause,
            } => Self::Internal {
                code,
                message: format!("{context}: {message}"),
                source_code,
                span,
                cause,
            },
            Self::Unsupported {
                code,
                message,
                source_code,
                span,
                cause,
            } => Self::Unsupported {
                code,
                message: format!("{context}: {message}"),
                source_code,
                span,
                cause,
            },
            Self::Error {
                code,
                message,
                source_code,
                span,
                cause,
            } => Self::Error {
                code,
                message: format!("{context}: {message}"),
                source_code,
                span,
                cause,
            },
        }
    }

    fn code(&self) -> ErrorCode {
        match self {
            Self::Internal { code, .. }
            | Self::Unsupported { code, .. }
            | Self::Error { code, .. } => *code,
        }
    }

    fn source_and_span(
        &self,
    ) -> (
        Option<&NamedSource<String>>,
        Option<&SourceSpan>,
        &'static str,
    ) {
        match self {
            Self::Internal {
                source_code, span, ..
            } => (
                source_code.as_ref(),
                span.as_ref(),
                "internal failure at this instruction",
            ),
            Self::Unsupported {
                source_code, span, ..
            } => (
                source_code.as_ref(),
                span.as_ref(),
                "unsupported instruction",
            ),
            Self::Error {
                source_code, span, ..
            } => (
                source_code.as_ref(),
                span.as_ref(),
                "translation failed here",
            ),
        }
    }
}

impl Diagnostic for Error {
    fn code<'a>(&'a self) -> Option<Box<dyn Display + 'a>> {
        Some(Box::new(self.code().to_string()))
    }

    fn source_code(&self) -> Option<&dyn SourceCode> {
        self.source_and_span()
            .0
            .map(|source| source as &dyn SourceCode)
    }

    fn labels(&self) -> Option<Box<dyn Iterator<Item = LabeledSpan> + '_>> {
        let (_, span, label) = self.source_and_span();
        span.map(|span| {
            Box::new(std::iter::once(LabeledSpan::new_primary_with_span(
                Some(label.to_owned()),
                *span,
            ))) as Box<dyn Iterator<Item = LabeledSpan>>
        })
    }
}

pub trait Context<T> {
    fn context(self, context: impl Display) -> Result<T>;
    fn with_context<F, C>(self, context: F) -> Result<T>
    where
        F: FnOnce() -> C,
        C: Display;
}

impl<T, E: std::error::Error + Send + Sync + 'static> Context<T> for std::result::Result<T, E> {
    fn context(self, context: impl Display) -> Result<T> {
        self.map_err(|error| {
            let context = context.to_string();
            let boxed: Box<dyn std::any::Any + Send + Sync> = Box::new(error);
            match boxed.downcast::<Error>() {
                Ok(error) => (*error).prepend_context(&context),
                Err(boxed) => {
                    let error = *boxed.downcast::<E>().expect("context error type changed");
                    Error::general(context).with_source(Box::new(error))
                }
            }
        })
    }

    fn with_context<F, C>(self, context: F) -> Result<T>
    where
        F: FnOnce() -> C,
        C: Display,
    {
        self.context(context())
    }
}

impl<T> Context<T> for Option<T> {
    fn context(self, context: impl Display) -> Result<T> {
        self.ok_or_else(|| Error::general(context.to_string()))
    }

    fn with_context<F, C>(self, context: F) -> Result<T>
    where
        F: FnOnce() -> C,
        C: Display,
    {
        self.context(context())
    }
}

#[macro_export]
macro_rules! bail {
    ($($arg:tt)*) => { return Err($crate::error::Error::internal(format!($($arg)*))) };
}

#[macro_export]
macro_rules! unsupported {
    ($($arg:tt)*) => { return Err($crate::error::Error::unsupported(format!($($arg)*))) };
}

#[macro_export]
macro_rules! ensure {
    ($condition:expr, $($arg:tt)*) => {
        if !$condition { $crate::bail!($($arg)*); }
    };
}
