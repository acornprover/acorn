use super::*;

impl Environment {
    /// Adds a forall statement to the environment.
    pub(super) fn add_forall_statement(
        &mut self,
        project: &dyn ProjectLookup,
        statement: &Statement,
        forall_statement: &ForAllStatement,
    ) -> error::Result<()> {
        if forall_statement.body.statements.is_empty() {
            return Ok(());
        }
        let mut args = vec![];
        for quantifier in &forall_statement.quantifiers {
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
            Some(&forall_statement.body),
        )?;

        let (outer_claim, range) =
            block.externalize_last_claim(self, &forall_statement.body.right_brace)?;
        let source = Source::anonymous(self.module_id, range, self.depth);
        let prop = Proposition::new(outer_claim, vec![], source);
        let index = self.add_node(Node::block(project, self, block, Some(prop)));
        self.add_node_lines(index, &statement.range());
        Ok(())
    }

    /// Adds an if statement to the environment.
    pub(super) fn add_if_statement(
        &mut self,
        project: &dyn ProjectLookup,
        statement: &Statement,
        if_statement: &IfStatement,
    ) -> error::Result<()> {
        let mut evaluator = self.evaluator(project);
        let condition =
            evaluator.evaluate_value(&if_statement.condition, Some(&AcornType::Bool))?;
        let local_obligations = evaluator.take_local_obligations();
        self.add_local_obligations(project, &[], local_obligations)?;
        let range = if_statement.condition.range();
        let if_claim = self.add_conditional(
            project,
            condition.clone(),
            range,
            &statement.first_token,
            &statement.last_token,
            &if_statement.body,
            None,
        )?;
        if let Some(else_body) = &if_statement.else_body {
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
        project: &dyn ProjectLookup,
        statement: &Statement,
        match_statement: &MatchStatement,
    ) -> error::Result<()> {
        let mut evaluator = self.evaluator(project);
        let scrutinee = evaluator.evaluate_value(&match_statement.scrutinee, None)?;
        let local_obligations = evaluator.take_local_obligations();
        self.add_local_obligations(project, &[], local_obligations)?;
        let scrutinee_type = scrutinee.get_type();
        let mut indices = vec![];
        let mut disjuncts = vec![];
        for (pattern, body) in &match_statement.cases {
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
                if match_statement.cases.len() > total {
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
        Err(match_statement
            .scrutinee
            .error("not all cases are covered in match statement"))
    }
}
