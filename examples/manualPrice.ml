open Bound.Expr

let t1 = from_string "floor((startPrice - minimumPrice) / (endTime - startTime)) - drop"
let t2 = from_string "(t1 - startTime) drop - diff1"
let t3 = from_string "startPrice - diff1 - price1"

let vars_to_keep = ["minimumPrice"; "startPrice"; "startTime"; "endTime"; "t1"]

let tupper = Bound.EqRewriter.rewrite [t1;t2;t3] 
									  [
									  	from_string "startPrice - minimumPrice";
									  	from_string "endTime - startTime";
									  	from_string "t1 - startTime";
									  	from_string "floor((startPrice - minimumPrice) / (endTime - startTime)) + 1 - ((startPrice - minimumPrice) / (endTime - startTime))"; (* floor lower bound rule *)
									  	from_string "(startPrice - minimumPrice) / (endTime - startTime)"; (* division rule *)
									  ] 
									  vars_to_keep 
									  (from_string "price1")

let tlower = Bound.EqRewriter.rewrite [t1;t2;t3] 
									  [
									  	from_string "startPrice - minimumPrice";
									  	from_string "endTime - startTime";
									  	from_string "t1 - startTime";
									  	from_string "endTime - t1";
									  	from_string "((startPrice - minimumPrice) / (endTime - startTime)) - floor((startPrice - minimumPrice) / (endTime - startTime))"; (* floor upper bound rule *)
									  	from_string "(startPrice - minimumPrice) / (endTime - startTime)"; (* division rule *)
									  ] 
									  vars_to_keep 
									  (from_string "-price1")

let t1_2 = from_string "floor((startPrice - minimumPrice) / (endTime - startTime)) - drop"
let t2_2 = from_string "(t2 - startTime) drop - diff2"
let t3_2 = from_string "startPrice - diff2 - price2"

let vars_to_keep_2 = "telapsed" :: vars_to_keep

let tmonotone = Bound.EqRewriter.rewrite [t1;t2;t3;t1_2;t2_2;t3_2;] 
									  [
									  	from_string "startPrice - minimumPrice";
									  	from_string "endTime - startTime";
									  	from_string "t1 - startTime";
									  	from_string "t2 - t1";
									  	from_string "endTime - t2";
									  	from_string "((startPrice - minimumPrice) / (endTime - startTime)) - floor((startPrice - minimumPrice) / (endTime - startTime))"; (* floor upper bound rule *)
									  	from_string "floor((startPrice - minimumPrice) / (endTime - startTime)) + 1 - ((startPrice - minimumPrice) / (endTime - startTime))"; (* floor lower bound rule *)
									  	from_string "(startPrice - minimumPrice) / (endTime - startTime)"; (* division rule *)
									  ] 
									  vars_to_keep 
									  (from_string "price2 - price1")