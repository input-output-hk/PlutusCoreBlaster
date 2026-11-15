use cardano/script_context.{ScriptContext}
use aiken/collection/list

validator schema_probe(context: ScriptContext) {
  else(_) { list.length(context.transaction.inputs) > 0 }
}
