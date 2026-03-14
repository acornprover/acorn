use super::*;

impl Environment {
    /// Adds a forall statement to the environment.
    pub(super) fn add_forall_statement(
        &mut self,
        project: &mut Project,
        statement: &Statement,
        fas: &ForAllStatement,
    ) -> error::Result<()> {
        if fas.body.statements.is_empty() {
            return Ok(());
        }
        let mut args = vec![];
        for quantifier in &fas.quantifiers {
            if let Declaration::Typed(name_token, _) = quantifier {
                self.bindings
                    .check_unqualified_name_available(&name_token.to_string(), name_token)?;
            }
            let (arg_name, arg_type) = self.evaluator(project).evaluate_declaration(quantifier)?;
            args.push((arg_name, arg_type));
        }

        let block = Block::new(
            project,
            &self,
            vec![],
            args,
            BlockParams::ForAll,
            &statement.first_token,
            &statement.last_token,
            Some(&fas.body),
        )?;

        let (outer_claim, range) = block.externalize_last_claim(self, &fas.body.right_brace)?;
        let source = Source::anonymous(self.module_id, range, self.depth);
        let prop = Proposition::new(outer_claim, vec![], source);
        let index = self.add_node(Node::block(project, self, block, Some(prop)));
        self.add_node_lines(index, &statement.range());
        Ok(())
    }

    /// Adds an if statement to the environment.
    pub(super) fn add_if_statement(
        &mut self,
        project: &mut Project,
        statement: &Statement,
        is: &IfStatement,
    ) -> error::Result<()> {
        let condition = self
            .evaluator(project)
            .evaluate_value(&is.condition, Some(&AcornType::Bool))?;
        let range = is.condition.range();
        let if_claim = self.add_conditional(
            project,
            condition.clone(),
            range,
            &statement.first_token,
            &statement.last_token,
            &is.body,
            None,
        )?;
        if let Some(else_body) = &is.else_body {
            self.add_conditional(
                project,
                condition.negate(),
                range,
                &else_body.left_brace,
                &else_body.right_brace,
                else_body,
                if_claim,
            )?;
        }
        Ok(())
    }

    /// Adds a match statement to the environment.
    pub(super) fn add_match_statement(
        &mut self,
        project: &mut Project,
        statement: &Statement,
        ms: &MatchStatement,
    ) -> error::Result<()> {
        let scrutinee = self
            .evaluator(project)
            .evaluate_value(&ms.scrutinee, None)?;
        let scrutinee_type = scrutinee.get_type();
        let mut indices = vec![];
        let mut disjuncts = vec![];
        for (pattern, body) in &ms.cases {
            let (constructor, args, i, total) = self
                .evaluator(project)
                .evaluate_pattern(&scrutinee_type, pattern)?;
            if indices.contains(&i) {
                return Err(pattern.error("duplicate pattern in match statement"));
            }
            indices.push(i);

            let params =
                BlockParams::MatchCase(scrutinee.clone(), constructor, args, pattern.range());

            let block = Block::new(
                project,
                &self,
                vec![],
                vec![],
                params,
                &body.left_brace,
                &body.right_brace,
                Some(body),
            )?;

            let (disjunct, _) = block.externalize_last_claim(self, &body.right_brace)?;
            disjuncts.push(disjunct);

            if total == indices.len() {
                if ms.cases.len() > total {
                    continue;
                }

                let disjunction = AcornValue::reduce(BinaryOp::Or, disjuncts);
                let source = Source::anonymous(self.module_id, statement.range(), self.depth);
                let prop = Proposition::new(disjunction, vec![], source);
                let index = self.add_node(Node::block(project, self, block, Some(prop)));
                self.add_node_lines(index, &body.range());
                return Ok(());
            }

            let index = self.add_node(Node::block(project, self, block, None));
            self.add_node_lines(index, &body.range());
        }
        Err(ms
            .scrutinee
            .error("not all cases are covered in match statement"))
    }
}
