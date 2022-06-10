open Bound.Expr

let _ = Bound.Log.log_time "Rewrite upper" (Bound.Rewriter.rewrite ~sat:3 [] 
						  [
							from_string "x"
						  ] 
						  ["y"])
   						  [from_string "y-floor(x)"];;