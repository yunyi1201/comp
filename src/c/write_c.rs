use itertools::Itertools;
use lang_c::ast::*;
use lang_c::span::Node;

use core::ops::Deref;
use std::io::{Result, Write};

use crate::write_base::*;

impl<T: WriteLine> WriteLine for Node<T> {
    fn write_line(&self, indent: usize, write: &mut dyn Write) -> Result<()> {
        self.node.write_line(indent, write)
    }
}

impl<T: WriteString> WriteString for Node<T> {
    fn write_string(&self) -> String {
        self.node.write_string()
    }
}

impl<T: WriteString> WriteString for Box<T> {
    fn write_string(&self) -> String {
        self.deref().write_string()
    }
}

impl<T: WriteString> WriteString for &T {
    fn write_string(&self) -> String {
        (*self).write_string()
    }
}

impl<T: WriteString> WriteString for Option<T> {
    fn write_string(&self) -> String {
        if let Some(this) = self {
            this.write_string()
        } else {
            "".to_string()
        }
    }
}

impl WriteLine for TranslationUnit {
    fn write_line(&self, indent: usize, write: &mut dyn Write) -> Result<()> {
        write_indent(indent, write)?;
        for external_decl in &self.0 {
            external_decl.write_line(indent, write)?;
        }
        Ok(())
    }
}

impl WriteLine for ExternalDeclaration {
    fn write_line(&self, indent: usize, write: &mut dyn Write) -> Result<()> {
        write_indent(indent, write)?;
        match self {
            ExternalDeclaration::Declaration(declaration) => {
                // println!("{}", declaration.write_string());
                writeln!(write, "{};", declaration.write_string())?
            }
            ExternalDeclaration::FunctionDefinition(def_f) => def_f.write_line(indent, write)?,
            _ => todo!(),
        }
        Ok(())
    }
}

impl WriteLine for FunctionDefinition {
    fn write_line(&self, indent: usize, write: &mut dyn Write) -> Result<()> {
        write_indent(indent, write)?;
        write!(
            write,
            "{} {} ",
            self.specifiers
                .iter()
                .map(|sepc| sepc.write_string())
                .join(" "),
            self.declarator.write_string()
        )?;
        self.statement.write_line(indent, write)?;
        Ok(())
    }
}

impl WriteLine for Statement {
    fn write_line(&self, indent: usize, write: &mut dyn Write) -> Result<()> {
        match self {
            Statement::Compound(comp_items) => {
                write_indent(indent, write)?;
                writeln!(write, "{{")?;
                for item in comp_items {
                    item.write_line(indent + 1, write)?;
                }
                write_indent(indent, write)?;
                writeln!(write, "}}")?;
            }
            Statement::Return(expr @ Some(_)) => {
                write_indent(indent, write)?;
                writeln!(write, "return {};", expr.write_string())?;
            }

            Statement::If(if_stmt) => {
                if_stmt.write_line(indent, write)?;
            }

            Statement::Switch(sw_stmt) => {
                sw_stmt.write_line(indent, write)?;
            }

            Statement::While(wh_stmt) => {
                wh_stmt.write_line(indent, write)?;
            }

            Statement::For(for_stmt) => {
                for_stmt.write_line(indent, write)?;
            }

            Statement::DoWhile(dwh_stmt) => {
                dwh_stmt.write_line(indent, write)?;
            }

            Statement::Break => {
                write_indent(indent, write)?;
                writeln!(write, "break;")?
            }
            Statement::Continue => {
                write_indent(indent, write)?;
                writeln!(write, "continue;")?
            }

            Statement::Expression(expr) => {
                write_indent(indent, write)?;
                writeln!(write, "{};", expr.write_string())?;
            }

            Statement::Labeled(labeled_stmt) => {
                labeled_stmt.write_line(indent, write)?;
            }

            _ => todo!(),
        }

        Ok(())
    }
}

impl WriteLine for LabeledStatement {
    fn write_line(&self, indent: usize, write: &mut dyn Write) -> Result<()> {
        write_indent(indent, write)?;
        writeln!(write, "{}:", self.label.write_string())?;
        self.statement.write_line(indent, write)?;
        Ok(())
    }
}
impl WriteString for Label {
    fn write_string(&self) -> String {
        match self {
            Label::Identifier(ident) => ident.write_string(),
            Label::Case(case_expr) => format!("case {}", case_expr.write_string()),
            Label::Default => "default".to_string(),
            _ => todo!(),
        }
    }
}
impl WriteLine for DoWhileStatement {
    fn write_line(&self, indent: usize, write: &mut dyn Write) -> Result<()> {
        write_indent(indent, write)?;
        writeln!(write, "do")?;
        self.statement.write_line(indent, write)?;
        write_indent(indent, write)?;
        writeln!(write, "while ({});", self.expression.write_string())?;
        Ok(())
    }
}

impl WriteLine for ForStatement {
    fn write_line(&self, indent: usize, write: &mut dyn Write) -> Result<()> {
        write_indent(indent, write)?;
        write!(
            write,
            "for ({}; {}; {}) ",
            self.initializer.write_string(),
            self.condition.write_string(),
            self.step.write_string()
        )?;
        self.statement.write_line(indent, write)?;
        Ok(())
    }
}

impl WriteString for ForInitializer {
    fn write_string(&self) -> String {
        match self {
            ForInitializer::Empty => "".to_string(),
            ForInitializer::Declaration(decl) => decl.write_string(),
            ForInitializer::Expression(expr) => expr.write_string(),
            ForInitializer::StaticAssert(_assert) => todo!(),
        }
    }
}

impl WriteLine for WhileStatement {
    fn write_line(&self, indent: usize, write: &mut dyn Write) -> Result<()> {
        write_indent(indent, write)?;
        write!(write, "while ({})", self.expression.write_string())?;
        self.statement.write_line(indent, write)?;
        Ok(())
    }
}

impl WriteLine for IfStatement {
    fn write_line(&self, indent: usize, write: &mut dyn Write) -> Result<()> {
        write_indent(indent, write)?;
        write!(write, "if ({})", self.condition.write_string())?;
        self.then_statement.write_line(indent, write)?;
        if let Some(else_stmt) = &self.else_statement {
            write_indent(indent, write)?;
            write!(write, "else")?;
            else_stmt.write_line(indent, write)?;
        }
        Ok(())
    }
}

impl WriteLine for SwitchStatement {
    fn write_line(&self, indent: usize, write: &mut dyn Write) -> Result<()> {
        write_indent(indent, write)?;
        writeln!(write, "switch ({})", self.expression.write_string())?;
        self.statement.write_line(indent, write)?;
        Ok(())
    }
}

impl WriteLine for BlockItem {
    fn write_line(&self, indent: usize, write: &mut dyn Write) -> Result<()> {
        match self {
            BlockItem::Declaration(decl) => {
                write_indent(indent, write)?;
                writeln!(write, "{};", decl.write_string())?;
            }
            BlockItem::Statement(stmt) => stmt.write_line(indent, write)?,
            _ => todo!(),
        }
        Ok(())
    }
}

impl WriteString for Declaration {
    fn write_string(&self) -> String {
        format!(
            "{} {}",
            self.specifiers
                .iter()
                .map(|item| item.write_string())
                .join(" "),
            self.declarators
                .iter()
                .map(|item| item.write_string())
                .join(", ")
        )
    }
}

impl WriteString for DeclarationSpecifier {
    fn write_string(&self) -> String {
        match self {
            DeclarationSpecifier::StorageClass(storage_class) => storage_class.write_string(),
            DeclarationSpecifier::TypeSpecifier(type_specifier) => type_specifier.write_string(),
            DeclarationSpecifier::TypeQualifier(type_qualifier) => type_qualifier.write_string(),
            DeclarationSpecifier::Function(_function_specifier) => todo!(),
            DeclarationSpecifier::Alignment(_alignment_specifier) => todo!(),
            _ => todo!(),
        }
    }
}

impl WriteString for StorageClassSpecifier {
    fn write_string(&self) -> String {
        match self {
            StorageClassSpecifier::Auto => "auto".to_string(),
            StorageClassSpecifier::Register => "register".to_string(),
            StorageClassSpecifier::Static => "static".to_string(),
            StorageClassSpecifier::Extern => "extern".to_string(),
            StorageClassSpecifier::Typedef => "typedef".to_string(),
            _ => todo!(),
        }
    }
}

impl WriteString for TypeQualifier {
    fn write_string(&self) -> String {
        match self {
            TypeQualifier::Const => "const".to_string(),
            TypeQualifier::Restrict => "restrict".to_string(),
            TypeQualifier::Volatile => "volatile".to_string(),
            TypeQualifier::Atomic => "_Atomic".to_string(),
            _ => todo!(),
        }
    }
}

impl WriteString for TypeSpecifier {
    fn write_string(&self) -> String {
        match self {
            Self::Void => "void".to_string(),
            Self::Char => "char".to_string(),
            Self::Short => "short".to_string(),
            Self::Int => "int".to_string(),
            Self::Long => "long".to_string(),
            Self::Double => "double".to_string(),
            Self::Float => "float".to_string(),
            Self::Signed => "signed".to_string(),
            Self::Unsigned => "unsigned".to_string(),
            Self::Bool => "bool".to_string(),
            Self::Complex => "complex".to_string(),
            Self::Struct(struct_spec) => struct_spec.write_string(),
            Self::TypedefName(ident) => ident.write_string(),
            _ => todo!(),
        }
    }
}

impl WriteString for StructType {
    fn write_string(&self) -> String {
        let kind_str = match self.kind.node {
            StructKind::Struct => "struct",
            StructKind::Union => "union",
        };

        let identifier_str = if let Some(ref id) = self.identifier {
            format!(" {}", id.node.name)
        } else {
            String::new()
        };

        let declarations_str = if let Some(ref declarations) = self.declarations {
            let decls: Vec<String> = declarations
                .iter()
                .map(|decl| decl.write_string())
                .collect();
            let mut decls = decls.join("; ");
            decls.push_str(";");
            format!(" {{ {} }}", decls)
        } else {
            String::new()
        };

        format!("{}{}{}", kind_str, identifier_str, declarations_str)
    }
}

impl WriteString for StructDeclaration {
    fn write_string(&self) -> String {
        match self {
            StructDeclaration::Field(field) => field.write_string(),
            _ => panic!("StaticAssert is not supported"),
        }
    }
}

impl WriteString for StructDeclarator {
    fn write_string(&self) -> String {
        let declarator_str = if let Some(ref declarator) = self.declarator {
            declarator.write_string()
        } else {
            String::new()
        };

        let bit_width_str = if let Some(ref bit_width) = self.bit_width {
            format!(": {}", bit_width.write_string())
        } else {
            String::new()
        };

        format!("{}{}", declarator_str, bit_width_str)
    }
}

impl WriteString for StructField {
    fn write_string(&self) -> String {
        let specifiers: Vec<String> = self
            .specifiers
            .iter()
            .map(|spec| spec.write_string())
            .collect();
        let declarators: Vec<String> = self
            .declarators
            .iter()
            .map(|decl| decl.write_string())
            .collect();
        format!("{} {}", specifiers.join(" "), declarators.join(", "))
    }
}

impl WriteString for InitDeclarator {
    fn write_string(&self) -> String {
        if self.initializer.is_some() {
            format!(
                "{} = {}",
                self.declarator.write_string(),
                self.initializer.as_ref().unwrap().write_string()
            )
        } else {
            self.declarator.write_string()
        }
    }
}

impl WriteString for Declarator {
    fn write_string(&self) -> String {
        fn recur_func(kind: &Node<DeclaratorKind>, rest: &[Node<DerivedDeclarator>]) -> String {
            let kind_str = kind.write_string();
            let derived_str = rest.iter().map(|item| item.write_string()).join(" ");

            if let [Node { node, .. }, rest @ ..] = rest {
                if let DerivedDeclarator::Pointer(_) = node {
                    return format!("{} {}", node.write_string(), recur_func(kind, rest),);
                }
            }
            format!("{}{}", kind_str, derived_str)
        }
        recur_func(&self.kind, &self.derived[..])
    }
}

impl WriteString for DeclaratorKind {
    fn write_string(&self) -> String {
        match self {
            DeclaratorKind::Identifier(identifier) => identifier.write_string(),
            DeclaratorKind::Declarator(decl) => {
                format!("({})", decl.write_string())
            }
            DeclaratorKind::Abstract => "".to_string(),
        }
    }
}

impl WriteString for Identifier {
    fn write_string(&self) -> String {
        self.name.clone()
    }
}

impl WriteString for DerivedDeclarator {
    fn write_string(&self) -> String {
        match self {
            DerivedDeclarator::Pointer(pointer) => format!(
                "{}{}",
                "*",
                pointer
                    .iter()
                    .map(|qualifier| qualifier.write_string())
                    .join(" ")
            ),
            DerivedDeclarator::Array(array) => array.write_string(),
            DerivedDeclarator::Function(decl_f) => decl_f.write_string(),
            DerivedDeclarator::KRFunction(decl_kr_f) => format!(
                "({})",
                decl_kr_f
                    .iter()
                    .map(|ident| ident.write_string())
                    .join(", ")
            ),
            _ => todo!(),
        }
    }
}

impl WriteString for FunctionDeclarator {
    fn write_string(&self) -> String {
        if let _e @ Ellipsis::Some = &self.ellipsis {
            return format!(
                "({}){}",
                self.parameters
                    .iter()
                    .map(|param| param.write_string())
                    .join(", "),
                "..."
            );
        }
        format!(
            "({})",
            self.parameters
                .iter()
                .map(|param| param.write_string())
                .join(", "),
        )
    }
}

impl WriteString for ParameterDeclaration {
    fn write_string(&self) -> String {
        format!(
            "{} {}",
            self.specifiers
                .iter()
                .map(|item| item.write_string())
                .join(" "),
            self.declarator.write_string()
        )
    }
}

impl WriteString for PointerQualifier {
    fn write_string(&self) -> String {
        match self {
            PointerQualifier::TypeQualifier(type_qualifier) => type_qualifier.write_string(),
            _ => todo!(),
        }
    }
}

impl WriteString for ArrayDeclarator {
    fn write_string(&self) -> String {
        format!(
            "{}[{}]",
            self.qualifiers
                .iter()
                .map(|qualiter| qualiter.write_string())
                .join(" "),
            self.size.write_string()
        )
    }
}

impl WriteString for ArraySize {
    fn write_string(&self) -> String {
        match self {
            ArraySize::Unknown => "".to_string(),
            ArraySize::VariableUnknown => "*".to_string(),
            ArraySize::VariableExpression(expr) => expr.write_string(),
            _ => todo!(),
        }
    }
}

impl WriteString for Initializer {
    fn write_string(&self) -> String {
        match self {
            Initializer::Expression(expr) => expr.write_string(),
            Initializer::List(list) => format!(
                "{{{}}}",
                list.iter().map(|item| item.write_string()).join(", ")
            ),
        }
    }
}

impl WriteString for Expression {
    fn write_string(&self) -> String {
        match self {
            Expression::Constant(c) => c.write_string(),
            Expression::Identifier(ident) => ident.write_string(),
            Expression::StringLiteral(s) => s.as_ref().node.concat(),
            Expression::BinaryOperator(bin_expr) => bin_expr.write_string(),
            Expression::Call(call_expr) => call_expr.write_string(),
            Expression::Cast(cast_expr) => cast_expr.write_string(),
            Expression::Comma(comma_expr) => format!(
                "({})",
                comma_expr.iter().map(|exp| exp.write_string()).join(", ")
            ),
            Expression::Conditional(cond_expr) => cond_expr.write_string(),
            Expression::UnaryOperator(unary_expr) => unary_expr.write_string(),
            Expression::AlignOf(align_expr) => align_expr.write_string(),
            Expression::Member(mem_expr) => mem_expr.write_string(),
            Expression::OffsetOf(offset_expr) => offset_expr.write_string(),
            Expression::SizeOfTy(ty) => ty.write_string(),
            Expression::SizeOfVal(val) => val.write_string(),
            _ => panic!("not Implemented"),
        }
    }
}

impl WriteString for SizeOfVal {
    fn write_string(&self) -> String {
        format!("sizeof({})", self.0.write_string())
    }
}
impl WriteString for SizeOfTy {
    fn write_string(&self) -> String {
        format!("sizeof({})", self.0.write_string())
    }
}

impl WriteString for OffsetOfExpression {
    fn write_string(&self) -> String {
        todo!()
    }
}

impl WriteString for MemberExpression {
    fn write_string(&self) -> String {
        format!(
            "{}{}{}",
            self.expression.write_string(),
            self.operator.write_string(),
            self.identifier.write_string()
        )
    }
}

impl WriteString for MemberOperator {
    fn write_string(&self) -> String {
        match self {
            MemberOperator::Direct => ".".to_string(),
            MemberOperator::Indirect => "->".to_string(),
        }
    }
}

impl WriteString for AlignOf {
    fn write_string(&self) -> String {
        format!("_Alignof({})", self.0.write_string())
    }
}

impl WriteString for UnaryOperatorExpression {
    fn write_string(&self) -> String {
        match self.operator.node {
            UnaryOperator::PostDecrement | UnaryOperator::PostIncrement => {
                format!(
                    "({}{})",
                    self.operand.write_string(),
                    self.operator.write_string()
                )
            }
            _ => format!(
                "({}{})",
                self.operator.write_string(),
                self.operand.write_string()
            ),
        }
    }
}

impl WriteString for UnaryOperator {
    fn write_string(&self) -> String {
        match self {
            UnaryOperator::Address => "&".to_string(),
            UnaryOperator::Indirection => "*".to_string(),
            UnaryOperator::PostDecrement => "--".to_string(),
            UnaryOperator::PostIncrement => "++".to_string(),
            UnaryOperator::Complement => "~".to_string(),
            UnaryOperator::Negate => "!".to_string(),
            UnaryOperator::Plus => "+".to_string(),
            UnaryOperator::Minus => "-".to_string(),
            UnaryOperator::PreDecrement => "--".to_string(),
            UnaryOperator::PreIncrement => "++".to_string(),
        }
    }
}

impl WriteString for ConditionalExpression {
    fn write_string(&self) -> String {
        format!(
            "({} ? {} : {})",
            self.condition.write_string(),
            self.then_expression.write_string(),
            self.else_expression.write_string()
        )
    }
}

impl WriteString for InitializerListItem {
    fn write_string(&self) -> String {
        assert!(self.designation.is_empty(), "Designation is not supported");
        self.initializer.write_string()
    }
}

impl WriteString for CastExpression {
    fn write_string(&self) -> String {
        format!(
            "({}){}",
            self.type_name.write_string(),
            self.expression.write_string()
        )
    }
}

impl WriteString for TypeName {
    fn write_string(&self) -> String {
        format!(
            "{} {}",
            self.specifiers
                .iter()
                .map(|item| item.write_string())
                .join(" "),
            self.declarator.write_string()
        )
    }
}

impl WriteString for SpecifierQualifier {
    fn write_string(&self) -> String {
        match self {
            SpecifierQualifier::TypeSpecifier(type_specifier) => type_specifier.write_string(),
            SpecifierQualifier::TypeQualifier(type_qualifier) => type_qualifier.write_string(),
            _ => todo!(),
        }
    }
}

impl WriteString for CallExpression {
    fn write_string(&self) -> String {
        format!(
            "{}({})",
            self.callee.write_string(),
            self.arguments
                .iter()
                .map(|arg| arg.write_string())
                .join(", ")
        )
    }
}

impl WriteString for BinaryOperatorExpression {
    fn write_string(&self) -> String {
        match self.operator.node {
            BinaryOperator::Index => {
                format!("({}[{}])", self.lhs.write_string(), self.rhs.write_string())
            }
            _ => format!(
                "({} {} {})",
                self.lhs.write_string(),
                self.operator.write_string(),
                self.rhs.write_string()
            ),
        }
    }
}

impl WriteString for BinaryOperator {
    fn write_string(&self) -> String {
        match self {
            BinaryOperator::Plus => "+".to_string(),
            BinaryOperator::Minus => "-".to_string(),
            BinaryOperator::Multiply => "*".to_string(),
            BinaryOperator::Divide => "/".to_string(),
            BinaryOperator::Modulo => "%".to_string(),
            BinaryOperator::BitwiseAnd => "&".to_string(),
            BinaryOperator::BitwiseOr => "|".to_string(),
            BinaryOperator::BitwiseXor => "^".to_string(),
            BinaryOperator::ShiftLeft => "<<".to_string(),
            BinaryOperator::ShiftRight => ">>".to_string(),
            BinaryOperator::LogicalAnd => "&&".to_string(),
            BinaryOperator::LogicalOr => "||".to_string(),
            BinaryOperator::Less => "<".to_string(),
            BinaryOperator::Greater => ">".to_string(),
            BinaryOperator::LessOrEqual => "<=".to_string(),
            BinaryOperator::GreaterOrEqual => ">=".to_string(),
            BinaryOperator::Equals => "==".to_string(),
            BinaryOperator::NotEquals => "!=".to_string(),
            BinaryOperator::Assign => "=".to_string(),
            BinaryOperator::AssignBitwiseAnd => "&=".to_string(),
            BinaryOperator::AssignBitwiseOr => "|=".to_string(),
            BinaryOperator::AssignBitwiseXor => "^=".to_string(),
            BinaryOperator::AssignShiftLeft => "<<=".to_string(),
            BinaryOperator::AssignShiftRight => ">>=".to_string(),
            BinaryOperator::AssignPlus => "+=".to_string(),
            BinaryOperator::AssignMinus => "-=".to_string(),
            BinaryOperator::AssignMultiply => "*=".to_string(),
            BinaryOperator::AssignDivide => "/=".to_string(),
            BinaryOperator::AssignModulo => "%=".to_string(),
            _ => todo!(),
        }
    }
}

impl WriteString for Constant {
    fn write_string(&self) -> String {
        match self {
            Constant::Integer(i) => i.write_string(),
            Constant::Float(f) => f.write_string(),
            Constant::Character(s) => s.clone(),
        }
    }
}

impl WriteString for Integer {
    fn write_string(&self) -> String {
        let base_str = match self.base {
            IntegerBase::Decimal => "",
            IntegerBase::Octal => "0",
            IntegerBase::Hexadecimal => "0x",
            IntegerBase::Binary => "0b",
        };

        let size_str = match self.suffix.size {
            IntegerSize::Int => "",
            IntegerSize::Long => "l",
            IntegerSize::LongLong => "ll",
        };

        let unsigned_str = if self.suffix.unsigned { "u" } else { "" };
        let imaginary_str = if self.suffix.imaginary { "i" } else { "" };

        format!(
            "{}{}{}{}{}",
            base_str, self.number, size_str, unsigned_str, imaginary_str
        )
    }
}

impl WriteString for Float {
    fn write_string(&self) -> String {
        let base_str = match self.base {
            FloatBase::Decimal => "",
            FloatBase::Hexadecimal => "0x",
        };

        let suffix_str = match self.suffix.format {
            FloatFormat::Float => "f",
            FloatFormat::Double => "",
            FloatFormat::LongDouble => "l",
            _ => unimplemented!(),
        };

        let imaginary_str = if self.suffix.imaginary { "i" } else { "" };

        format!("{}{}{}{}", base_str, self.number, suffix_str, imaginary_str)
    }
}
