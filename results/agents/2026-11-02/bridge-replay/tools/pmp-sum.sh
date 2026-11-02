#!/bin/bash
sed 's/^#[0-9]* *0x[0-9a-f]* in //; s/^#[0-9]* *//; s/ (.*//' $1 | sed 's/kobayashi_marust::konclude_ht::completion::u[0-9]*::<impl kobayashi_marust::konclude_ht::completion::algorithm::CompletionTaskHandleAlgorithm>:://; s/kobayashi_marust::konclude_ht:://' | sort | uniq -c | sort -rn | head -${2:-45}
