theory Submission
  imports
    Defs
    Main
    "HOL-Data_Structures.Array_Specs"
    "HOL-Data_Structures.Cmp"
begin

section "Rope based on 2-3 Trees"

text "Hello there!
  My project deals with efficient (in terms of tree balance) representation of (string) ropes.
  
  ## Background
  If I may give some context and motivation for my project.
  I have a strong compiler construction background. Therefore, my original project attempt
  was to formalize something about compiler components, finding out that this is a very complex topic
  and covered in separate lecture.
  Consequentially, I wanted to pick a more data-structure-related topic to be a bit 'safer'.
  
  It really came down reading this StackOverflow response as the result to one of my Google queries: https://stackoverflow.com/a/562580.

  ## Related Work

  ### Usage
  I thought that ropes might actually be a nice connection to my compiler construction as the Wikipedia article
  highlighted its usefulness for text editors. I really only found out later that barely any
  of the popular IDEs use them.
  E.g., VSCode for example uses Piece Tables (https://code.visualstudio.com/blogs/2018/03/23/text-buffer-reimplementation),
  Emacs uses Gap Buffers (https://www.gnu.org/software/emacs/manual/html_node/elisp/Buffer-Gap.html).
  
  Two text editors that user ropes  internally are the
  Xi Editor (https://xi-editor.io) and Lapce (https://lapce.dev; https://github.com/lapce/lapce#readme)
  which both have a strong focus on text editing performance (The onde is kinda the successor the the other though).
  A writeup of the underlying architecture can be found here https://xi-editor.io/docs/rope_science_00.html.

  So this gives some context to the applicability and usage of Ropes.
  While I can't really assess the status quo,
  I wanted to provide those resources as an overview.

  ### Balancing
  The central paper that introduced ropes can be found here https://www.cs.tufts.edu/comp/150FP/archive/hans-boehm/ropes.pdf.
  They discuss balancing (and impacts of simple concatenation) in great detail. While they discussed issues
  of doing concatenation by just creating a new root node and present some methods to avoid creating a degenerated tree
  too quickly, implementations out there, even those that
  cite exactly this paper (https://github.com/fweez/SwiftRope), seem to just do concatenation
  without any balancing considerations (see Wikipedia article itself https://en.wikipedia.org/wiki/Rope_(data_structure),
  https://github.com/component/rope).

  ## Project
  Within this project I'm exploring the rope data structure by applying them to 2-3 trees which we
  heavily studied in the lecture. Using the 2-3 tree structure we apply the benefits of self-balancing
  trees to the rope data structure. Specifically, I implemented insert and concat operations
  that preserve the completeness of the rope.
"

subsection "Data type"

(*
EDIT: Note, inspired from typical representations I originally had the following representation of a `'a rope` where
I only stored the length of the left (or mid) subropes (see below).
datatype 'a rope = RLeaf "'a list" |
                   RNode2 nat "'a rope" "'a rope" |
                   RNode3 nat "'a rope" nat "'a rope" "'a rope"


While this representation is probably a nice trade of
between performance and memory consumption, it requires additional calls to `len_rope` both for insert (in most
of the recursive calls) and merge (once to get the length of the left-tree you merge with).
As we got a deadline extension, I decided to spend the extra time to try to reengineer the data structure
to include the length of all subtrees (as well as the leaf length as well).
*)

(* The nat in front of each sub-rope provides the length of that exact sub-rope. *)
datatype 'a rope = RLeaf nat "'a list" |
                   RNode2 nat "'a rope" nat "'a rope" |
                   RNode3 nat "'a rope" nat "'a rope" nat "'a rope"


subsection "Basic operations"

fun len_rope :: "'a rope \<Rightarrow> nat" where
  "len_rope (RLeaf len _) = len" |
  "len_rope (RNode2 llen _ rlen _) = llen + rlen" |
  "len_rope (RNode3 llen _ mlen _ rlen _) = llen + mlen + rlen"

(*Height function and instantiation taken from 2-3 trees*)
class height =
  fixes height :: "'a \<Rightarrow> nat"

instantiation rope :: (type)height
begin

fun height_rope :: "'a rope \<Rightarrow> nat" where
  "height_rope (RLeaf _ _) = 0" |
  "height_rope (RNode2 _ l _ r) = Suc (max (height_rope l) (height_rope r))" |
  "height_rope (RNode3 _ l _ m _ r) = Suc(max (height_rope l) (max (height_rope m) (height_rope r)))"

instance ..
end

(*The regular size method counts all the array elements in the Leaf node as well. We can't override that afaik? *)
fun size_rope :: "'a rope \<Rightarrow> nat" where
  "size_rope (RLeaf _ _) = 1" |
  "size_rope (RNode2 _ l _ r) = size_rope l + size_rope r + 1" |
  "size_rope (RNode3 _ l _ m _ r) = size_rope l + size_rope m + size_rope r + 1"

subsection "Invariants"

(*Ensure that the length property of every node is set correctly*)
fun invar :: "'a rope \<Rightarrow> bool" where
  "invar (RLeaf len xs) = (length xs = len)" |
  "invar (RNode2 llen l rlen r) = (len_rope l = llen \<and> len_rope r = rlen \<and> invar l \<and> invar r)" |
  "invar (RNode3 llen l mlen m rlen r) = (len_rope l = llen \<and> len_rope m = mlen \<and> len_rope r = rlen \<and>
                                        invar l \<and> invar m \<and> invar r)"

(*completeness taken from 23 trees*)
fun complete :: "'a rope \<Rightarrow> bool" where
  "complete (RLeaf _ _) = True" |
  "complete (RNode2 _ l _ r) = (height l = height r \<and> complete l \<and> complete r)" |
  "complete (RNode3 _ l _ m _ r) = (height l = height m \<and> height m = height r
                  \<and> complete l \<and> complete m \<and> complete r)"


subsection "Array operations"

fun inorder :: "'a rope \<Rightarrow> 'a list" where
  "inorder (RLeaf _ xs) = xs" |
  "inorder (RNode2 _ l _ r) = (inorder l) @ (inorder r)" |
  "inorder (RNode3 _ l _ m _ r) = (inorder l) @ (inorder m) @ (inorder r)"

(*
leaf creates a simple list RLeaf.
While primarily used for the Array interpretation. This can also be useful on its own for the general
flow of using the rope.
1. Construct a rope using this method for the whole string
2. The rope is automatically split into multiple nodes when doing e.g. insert operations on the
  data structure. Splitting the rope "as necessary". Otherwise, some implementations out there
  automatically split a leaf based on a certain threshold.
*)
fun leaf :: "'a list \<Rightarrow> 'a rope" where
  "leaf xs = RLeaf (length xs) xs"

(* A simple lookup operation to check for a single index-based lookup in the rope *)
fun lookup :: "'a rope \<Rightarrow> nat \<Rightarrow> 'a" where
  "lookup (RLeaf _ xs) i = xs ! i" |
  "lookup (RNode2 llen l _ r) i = (
          if i < llen then lookup l i
          else lookup r (i - llen))" |
  "lookup (RNode3 llen l mlen m _ r) i = (
          if i < llen then lookup l i
          else if (i-llen) < mlen then lookup m (i-llen)
          else lookup r (i-llen-mlen))"

(* Update a single character in the rope *)
fun update :: "nat \<Rightarrow> 'a \<Rightarrow> 'a rope \<Rightarrow> 'a rope" where 
  "update i a (RLeaf len xs) = RLeaf len (xs[i:=a])" |
  "update i a (RNode2 llen l rlen r) = (
          if i < llen then RNode2 llen (update i a l) rlen r
          else RNode2 llen l rlen (update (i - llen) a r))" |
  "update i a (RNode3 llen l mlen m rlen r) = (
          if i < llen then RNode3 llen (update i a l) mlen m rlen r
          else if (i-llen) < mlen then RNode3 llen l mlen (update (i-llen) a m) rlen r
          else RNode3 llen l mlen m rlen (update (i-llen-mlen) a r))"

subsubsection "Array interpretation proof"

lemma invar[simp]: "invar rs \<Longrightarrow> len_rope rs = length (inorder rs)"
  apply (induction rs)
  apply auto
  done

lemma len_update[simp]: "len_rope (update i a rs) = len_rope rs"
  apply (induction rs arbitrary: i a)
  apply auto
  done

lemma len_update_inorder[simp]: "length (inorder (update i a rs)) = length (inorder rs)"
  apply (induction rs arbitrary: i a)
  apply auto
  done

lemma invar_lookup: "invar rs \<Longrightarrow> i < len_rope rs \<Longrightarrow> lookup rs i = inorder rs ! i"
  apply (induction rs i rule: lookup.induct)
  apply (auto simp: nth_append)
  done

lemma invar_update_list: "invar rs \<Longrightarrow> i < len_rope rs \<Longrightarrow> inorder(update i a rs) = (inorder rs)[i:=a]"
  apply (induction i a rs rule: update.induct)
  apply (auto simp: list_update_append1 list_update_append)
  done

lemma rope_invar_update: "invar rs \<Longrightarrow> i < len_rope rs \<Longrightarrow> invar (update i a rs)"
  apply (induction rs arbitrary: a i)
  apply (auto)
  done

(*
Some thoughts and some context:
One might initially think that we could see our rope implementation as an refinement of a regular 
2-3 tree or just as a interpretation of the Set locale. However, this is not possible or sensible
as we are really only using the tree for storing metadata with the actual data being stored in the leafs.
Our values in the rope are basically the tuple of a substring and the corresponding location information
(the index in the whole data structure). The location information of an element is highly dynamic
and might change if an element is inserted.

What ropes really are (and nothing more) is an interpretation of an Array.
So this is what we do here.
*)
interpretation Array 
  where lookup = lookup and update = update and len = len_rope and array = leaf
    and list = inorder and invar = invar
proof (standard, goal_cases)
  case (1 ar n)
  then show ?case by (simp add: invar_lookup)
next
  case (2 ar n x)
  then show ?case by (simp add: invar_update_list)
next
  case (3 ar)
  then show ?case by simp
next
  case (4 xs)
  then show ?case by simp
next
  case (5 ar n x)
  then show ?case using rope_invar_update by fastforce
next
  case (6 xs)
  then show ?case by simp
qed

subsection "Flexible Array implementation"

text "This section plays around with interpretations a bit. Specifically, we play around with
  the Array_Flex locale and see how that applies to our rope implementation.
  Those operations are distinct from the rope specific operations as they solely rely on the
  'Array functionality' of the rope and don't change the tree structure itself."

fun prepend_elem :: "'a \<Rightarrow> 'a rope \<Rightarrow> 'a rope" where
  "prepend_elem a (RLeaf len rs) = RLeaf (len+1) (a#rs)" |
  "prepend_elem a (RNode2 llen l rlen r) = RNode2 (llen + 1) (prepend_elem a l) rlen r" |
  "prepend_elem a (RNode3 llen l mlen m rlen r) = RNode3 (llen + 1) (prepend_elem a l) mlen m rlen r"

fun del_head_elem :: "'a rope \<Rightarrow> 'a rope" where
  "del_head_elem (RLeaf len rs) = (if length rs > 0 then RLeaf (len-1) (tl rs) else RLeaf len rs)" |
  "del_head_elem (RNode2 llen l rlen r) = (
        if llen > 0 then RNode2 (llen -1) (del_head_elem l) rlen r
        else RNode2 llen l (rlen -1) (del_head_elem r))" |
  "del_head_elem (RNode3 llen l mlen m rlen r) = (
        if llen > 0 then RNode3 (llen -1) (del_head_elem l) mlen m rlen r
        else if mlen > 0 then RNode3 llen l (mlen-1) (del_head_elem m) rlen r
        else RNode3 llen l mlen m (rlen-1) (del_head_elem r))"

fun append_elem :: "'a \<Rightarrow> 'a rope \<Rightarrow> 'a rope" where 
  "append_elem a (RLeaf len rs) = RLeaf (len+1) (rs @ [a])" |
  "append_elem a (RNode2 llen l rlen r) = (RNode2 llen l (rlen+1) (append_elem a r))" |
  "append_elem a (RNode3 llen l mlen m rlen r) = (RNode3 llen l mlen m (rlen+1) (append_elem a r))"

fun del_tail_elem :: "'a rope \<Rightarrow> 'a rope" where
  "del_tail_elem (RLeaf len rs) = (if length rs > 0 then RLeaf (len-1) (butlast rs) else RLeaf len rs)" |
  "del_tail_elem (RNode2 llen l rlen r) = (
        if rlen > 0 then  RNode2 llen l (rlen-1) (del_tail_elem r)
        else RNode2 (llen -1) (del_tail_elem l) rlen r)" |
  "del_tail_elem (RNode3 llen l mlen m rlen r) = (
        if rlen > 0 then  RNode3 llen l mlen m (rlen-1) (del_tail_elem r)
        else if mlen > 0 then RNode3 llen l (mlen-1) (del_tail_elem m) rlen r
        else RNode3 (llen -1) (del_tail_elem l) mlen m rlen r)"

lemma prepend_elem_list: "invar rs \<Longrightarrow> inorder(prepend_elem a rs) = a # inorder rs"
  by (induction rs) auto
  
lemma del_head_elem_list: "invar rs \<Longrightarrow> inorder(del_head_elem rs) = tl (inorder rs)"
  by (induction rs) (auto)

lemma append_elem_list: "invar rs \<Longrightarrow> inorder(append_elem a rs) = inorder rs @ [a]"
  by (induction rs) auto

lemma del_tail_elem_list: "invar rs \<Longrightarrow> inorder(del_tail_elem rs) = butlast (inorder rs)"
  by (induction rs) (auto simp: butlast_append)

lemma invar_prepend_elem: "invar rs \<Longrightarrow> invar (prepend_elem a rs)"
  apply (induction  rs)
  apply (auto simp: prepend_elem_list)
  done

lemma invar_del_head_length: "invar rs \<Longrightarrow> length (inorder (del_head_elem rs)) = length (inorder rs) - 1"
  apply (induction rs)
  apply auto
  apply (simp add: add_eq_if)+
  done

lemma invar_del_head_elem: "invar rs \<Longrightarrow> invar (del_head_elem rs)"
  apply (induction rs)
  apply auto
  apply (auto simp: invar_del_head_length)
  done


lemma invar_append_elem: "invar rs \<Longrightarrow> invar (append_elem a rs)"
  apply (induction rs)
  apply (auto simp: append_elem_list)
  done

lemma invar_del_tail_length: "invar rs \<Longrightarrow> length (inorder (del_tail_elem rs)) = length (inorder rs) - 1"
  apply (induction rs)
  apply auto
  apply (auto simp: add.commute add_eq_if)+
  done

lemma invar_del_tail_elem: "invar rs \<Longrightarrow> invar (del_tail_elem rs)"
  apply (induction rs)
  apply auto
  apply (auto simp: del_tail_elem_list)
  done

interpretation Array_Flex
  where lookup = lookup and update = update and len = len_rope and array = leaf
    and add_lo = prepend_elem and del_lo = del_head_elem
      and add_hi = append_elem and del_hi = del_tail_elem
    and list = inorder and invar = invar
proof (standard, goal_cases)
  case (1 ar a)
  then show ?case by (simp add: prepend_elem_list)
next
  case (2 ar)
  then show ?case by (simp add: del_head_elem_list)
next
  case (3 ar a)
  then show ?case by (simp add: append_elem_list)
next
  case (4 ar)
  then show ?case by (simp add: del_tail_elem_list)
next
  case (5 ar a)
  then show ?case using invar_prepend_elem by fastforce
next
  case (6 ar)
  then show ?case using invar_del_head_elem by fastforce
next
  case (7 ar a)
  then show ?case using invar_append_elem by fastforce
next
  case (8 ar)
  then show ?case using invar_del_tail_elem by fastforce
qed

subsection "Rope operations"

text "This section implements the 'interesting' rope operations like insertion and concatenation.
  As you might expect this resembles the implementation of regular 2-3 trees with the exception
  that we have to take care for the length information present in the inner tree nodes."

(*
`upI` type inspired from tree23.
The nat's in the `OF` constructor encode the length of the rope that is written behind it.
You may note that the right rope doesn't have length information. That is, because it doesn't change
our reliance on `len_rope` in the implementation. This is discussed further below.
*)
datatype 'a upI = RI "'a rope" | OF "'a rope" "'a rope"

fun ropeI :: "'a upI \<Rightarrow> 'a rope" where
  "ropeI (RI rs) = rs" |
  "ropeI (OF l r) = RNode2 (len_rope l) l (len_rope r) r"

(* Splits a list at a given index and provides the sub lists in a tuple. *)
fun split_by_i :: "'a list \<Rightarrow> nat \<Rightarrow> ('a list \<times> 'a list)" where
  "split_by_i xs i = (take i xs, drop i xs)"

lemma split_by_i_elements: "(xs0, xs1) = split_by_i xs i \<Longrightarrow> xs = xs0 @ xs1"
  apply (induction xs) 
  apply auto
  done

lemma split_by_i_len: "i < length xs \<Longrightarrow> (xs0, xs1) = split_by_i xs i \<Longrightarrow> length xs0 = i"
  apply (induction xs arbitrary: xs0 xs1)
  apply auto
  done

text "ins_node inserts a a substring at a given index in the rope while keeping the tree in balance.
Inserting within a existing Leaf will split that leaf in two and the new string is appended to the left one.

NOTE: While we catch and gracefully handle indices larger than the length of the total string (making proofs
easier) it is not meant to be assumed correct and considered undefined behavior!

FUTURE WORK: We currently still use calls `len_rope` in three place which isn't optimal but already better
  than without augmenting the `upI` type. Future work could explore how introducing a third length
  parameter at the tree nodes could potentially reduce computing complexity and make this whole
  thing a bit more efficient.
"

fun ins_node :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a rope \<Rightarrow> 'a upI" where
  (* empty leafs get replaced*)
  "ins_node i ys (RLeaf _ []) = RI (leaf ys)" |
  (*either we "append" to the right if index is larger, or we split the node at index i
    and append the new list to the left part and create a new node with the rest*)
  "ins_node i ys (RLeaf len  xs) = (
      if i > length xs then OF (RLeaf len xs) (RLeaf (length ys) ys)
      else (let (l,r) = split_by_i xs i in
         OF (RLeaf (length ys + i) (l@ ys)) (RLeaf (len -i) r)))" | (* on which side we append/prepend is arbitrary.*)
  "ins_node i ys (RNode2 llen l lenr r) = (
          if i < llen then
            (case ins_node i ys l of
              RI l' \<Rightarrow> RI (RNode2 (llen + length ys) l' lenr r) |
              OF l1 l2 \<Rightarrow> RI (RNode3 (len_rope l1) l1 (len_rope l2) l2 lenr r))
          else
            (case ins_node (i-llen) ys r of
              RI r' \<Rightarrow> RI (RNode2 llen l (len_rope r') r') |
              OF r1 r2 \<Rightarrow> RI (RNode3 llen l (len_rope r1) r1 (len_rope r2) r2)))" |
  "ins_node i ys (RNode3 llen l mlen m rlen r) = (
          if i < llen then
            (case ins_node i ys l of
              RI l' \<Rightarrow> RI (RNode3 (llen + length ys) l' mlen m rlen r) |
              OF l1 l2 \<Rightarrow> OF (RNode2 (len_rope l1) l1 (len_rope l2) l2) (RNode2 mlen m rlen r))
          else if i < (llen + mlen) then
            (case ins_node (i-llen) ys m of
              RI m' \<Rightarrow> RI (RNode3 llen l (mlen + length ys) m' rlen r) |
              OF m1 m2 \<Rightarrow> OF (RNode2 llen l (len_rope m1) m1) (RNode2 (len_rope m2) m2 rlen r))
          else
            (case ins_node (i-llen-mlen) ys r of
              RI r' \<Rightarrow> RI (RNode3 llen l mlen m (len_rope r') r') |
              OF r1 r2 \<Rightarrow> OF (RNode2 llen l mlen m) (RNode2 (len_rope r1) r1 (len_rope r2) r2)))"


definition insert_node :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a rope \<Rightarrow> 'a rope" where
  "insert_node i ys rs = ropeI (ins_node i ys rs)"

text "Below are all parts required for implementation of the `join` function (used by the concat definition).
  In turns out, what we did in Exercise09 for 2-3 trees, can be similarly applied to our rope implementation
  (as we don't have elements in the tree nodes itself) resulting in a very elegant and concise join implementation."

(*
Note: I had a version implemented where `joinL` accepted a `llen` parameter removing the need for on the fly
  computations of `len_rope llen` and making the whole thing really efficient. However, this version 
  made it impossible to prove the whole thing. This may again motivate a version of the rope data type
  that includes the length of the rightmost child tree as well
*)
fun joinL :: "'a rope \<Rightarrow> 'a rope \<Rightarrow> 'a upI" where
  "joinL l r = (
    if height l = height r then
      OF l r
    else (case r of
      RLeaf len xs \<Rightarrow> undefined |
      RNode2 llenr lr rlenr rr \<Rightarrow> (case joinL l lr of
        RI l' \<Rightarrow> RI (RNode2 (len_rope l + llenr) l' rlenr rr) |
        OF l' r' \<Rightarrow> RI (RNode3 (len_rope l') l' (len_rope r') r' rlenr rr)) |
      RNode3 llenr lr mlenr mr rlenr rr \<Rightarrow> (case joinL l lr of
        RI l' \<Rightarrow> RI (RNode3 (len_rope l') l' mlenr mr rlenr rr) |
        OF l' r' \<Rightarrow> OF (RNode2 (len_rope l') l' (len_rope r') r') (RNode2 mlenr mr rlenr rr)))
    )"

fun joinR :: "'a rope \<Rightarrow> 'a rope \<Rightarrow> 'a upI" where 
  "joinR l r = (
    if height l = height r then
      OF l r
    else (case l of
      RNode2 llenl ll rlenl rl \<Rightarrow> (case joinR rl r of
        RI r' \<Rightarrow> RI (RNode2 llenl ll (len_rope r') r') |
        OF l' r' \<Rightarrow> RI (RNode3 llenl ll (len_rope l') l' (len_rope r') r')) |
      RNode3 llenl ll mlenl ml rlenl rl \<Rightarrow> (case joinR rl r of
        RI r' \<Rightarrow> RI (RNode3 llenl ll mlenl ml (len_rope r') r') |
        OF l' r' \<Rightarrow> OF (RNode2 llenl ll mlenl ml) (RNode2 (len_rope l') l' (len_rope r') r')))
    )"

fun concat :: "'a rope \<Rightarrow> 'a rope \<Rightarrow> 'a upI" where
  "concat l r = (case cmp (height l) (height r) of
    LT \<Rightarrow> joinL l r |
    EQ \<Rightarrow> OF l r |
    GT \<Rightarrow> joinR l r)"

subsubsection "Functional correctness"

(* INSERT *)

fun ins_list :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "ins_list i ys xs = take i xs @ ys @ drop i xs"

lemma ins_node_list: "invar rs \<Longrightarrow> inorder (ropeI (ins_node i ys rs)) = ins_list i ys (inorder rs)"
  apply (induction i ys rs rule: ins_node.induct)
  apply auto (* In runs faster if we just do auto first *)
  apply (auto split: upI.splits)
  done

lemma insert_node_list: "invar rs \<Longrightarrow> inorder (insert_node i ys rs) = ins_list i ys (inorder rs)"
  by (simp add: ins_node_list insert_node_def)

lemma ins_node_len_rope_length[simp]: "invar rs \<Longrightarrow> len_rope (ropeI (ins_node i ys rs)) = len_rope rs + length ys"
  apply (induction i ys rs rule: ins_node.induct)
  apply (auto split: upI.splits)
  done

lemma ins_node_length_rope_length[simp]: "invar rs \<Longrightarrow> length (inorder (ropeI (ins_node i ys rs))) = len_rope rs + length ys"
  apply (induction i ys rs rule: ins_node.induct)
  apply (auto split: upI.splits)
  done

lemma ins_node_invar: "invar rs \<Longrightarrow> invar (ropeI (ins_node i ys rs))"
  apply (induction i ys rs rule: ins_node.induct)
  apply auto
  apply (auto split: upI.splits)
  by (metis ins_node_len_rope_length invar ropeI.simps(1))+

lemma insert_node_invar: "invar rs \<Longrightarrow> invar (insert_node i ys rs)"
  by (simp add: ins_node_invar insert_node_def)

(* JOIN L *)

lemma joinL_inorder:
  fixes l r :: "'a rope"
  assumes "height l < height r"
  assumes "complete l" "complete r"
  shows "inorder (ropeI (joinL l r)) = (inorder l @ inorder r)"
  using assms
  apply (induction r)
  apply (auto split: upI.split)
  done

lemma joinL_length:
  fixes l r :: "'a rope"
  assumes "height l < height r"
  assumes "complete l" "complete r"
  assumes "invar l" "invar r"
  shows "len_rope (ropeI (joinL l r)) = len_rope l + len_rope r"
  using assms
  apply (induction r)
  apply (auto split: upI.splits)
  done

lemma joinL_invar:
  fixes l r :: "'a rope"
  assumes "height l < height r"
  assumes "complete l" "complete r"
  assumes "invar l" "invar r"
  shows "invar (ropeI (joinL l r))"
  using assms
  apply (induction r)
  apply (auto split: upI.split)
  using joinL_length apply force+
  done

(* JOIN R *)

lemma joinR_inorder:
  fixes l r :: "'a rope"
  assumes "height l > height r"
  assumes "complete l" "complete r"
  shows "inorder (ropeI (joinR l r)) = (inorder l @ inorder r)"
  using assms
  apply (induction l)
  apply (auto split: upI.split)
  done

lemma joinR_invar:
  fixes l r :: "'a rope"
  assumes "height l > height r"
  assumes "complete l" "complete r"
  assumes "invar l" "invar r"
  shows "invar (ropeI (joinR l r))"
  using assms
  apply (induction l)
  apply (auto split: upI.splits)
  done

(* CONCAT *)

lemma concat_inorder:
  fixes l r :: "'a rope"
  assumes "complete l" "complete r"
  shows "inorder (ropeI (concat l r)) = (inorder l @ inorder r)"
  using assms joinL_inorder joinR_inorder
  apply (induction l r rule: concat.induct)
  apply fastforce+
  done

lemma concat_invar:
  fixes l r :: "'a rope"
  assumes "complete l" "complete r"
  assumes "invar l" "invar r"
  shows "invar (ropeI (concat l r))"
  using assms joinL_invar joinR_invar
  apply (induction l r rule: concat.induct)
  apply (auto split: upI.splits)
  apply fastforce+
  done

subsubsection "Completeness Proofs"

(*taken from tree23*)
fun hI :: "'a upI \<Rightarrow> nat" where
  "hI (RI t) = height t" |
  "hI (OF l _) = height l"

(* INSERT *)

lemma ins_complete: "invar rs \<Longrightarrow> complete rs \<Longrightarrow> complete (ropeI (ins_node i ys rs)) \<and> hI(ins_node i ys rs) = height rs"
  apply (induction i ys rs rule: ins_node.induct)
  apply auto (* In runs faster if we just do auto first *)
  apply (auto split: upI.splits)
  done

lemma insert_complete: "invar rs \<Longrightarrow> complete rs \<Longrightarrow> complete (insert_node i ys rs)"
  by (simp add: ins_complete insert_node_def)

(* JOIN L *)

lemma joinL_complete:
  fixes l r :: "'a rope"
  assumes "height l < height r"
  assumes "complete l" "complete r"
  shows "complete (ropeI (joinL l r)) \<and> hI (joinL l r) = height r"
  using assms
  apply (induction r)
  apply (auto split: upI.split)
  done

(* JOIN R *)

lemma joinR_complete:
  fixes l r :: "'a rope"
  assumes "height l > height r"
  assumes "complete l" "complete r"
  shows "complete (ropeI (joinR l r)) \<and> hI (joinR l r) = height l"
  using assms
  apply (induction l)
  apply (auto split: upI.split)
  done

(* CONCAT *)

lemma concat_complete:
  fixes l r :: "'a rope"
  assumes "complete l" "complete r"
  shows "complete (ropeI (concat l r))"
  using assms joinL_complete joinR_complete
  apply (induction l r rule: concat.induct)
  apply fastforce+
  done

subsubsection "Time complexity"

fun T_height :: "'a rope \<Rightarrow> nat" where
  "T_height (RLeaf _ _) = 1" |
  "T_height (RNode2 _ l _ r) = T_height l + T_height r + 1" |
  "T_height (RNode3 _ l _ m _ r) = T_height l + T_height m + T_height r + 1"

(* T_height is basically equivalent to size_rope. So no surprises *)
lemma T_height_bound: "T_height rs = size_rope rs"
  by (induction rs) auto

(* First, we look at a simplified version of the time complexity function where we don't
  consider calls to `height`. *)
fun T_joinL_simp :: "'a rope \<Rightarrow> 'a rope \<Rightarrow> nat" where
  "T_joinL_simp l r = (
      if height l = height r then 1
      else (case r of
      RNode2 llenr lr rlenr rr \<Rightarrow> T_joinL_simp l lr |
      RNode3 llenr lr mlenr mr rlenr rr \<Rightarrow> T_joinL_simp l lr) + 1)"


(* We show that the simplified join is basically linear in the height difference of the two trees. *)
lemma joinL_simp_time:
  fixes l r :: "'a rope"
  assumes "height l < height r"
  assumes "complete l" "complete r"
  assumes "invar l" "invar r"
  shows "T_joinL_simp l r = height r - height l + 1"
  using assms
  apply (induction r)
  apply auto
  done

(* To formulate it by a bound *)
lemma joinL_simp_bound[]:
  fixes l r :: "'a rope"
  assumes "height l < height r"
  assumes "complete l" "complete r"
  assumes "invar l" "invar r"
  shows "T_joinL_simp l r \<le> height r + 1"
  using assms
  using joinL_simp_time by fastforce

(*
As we are working with complete ropes, we can define a height function that only traverses the left subrope.
We are not using that in the actual implementation, but for the sake of the analysis we use the simplified version here.
And it would be easily replaceable anyways.
*)

fun T_height_complete :: "'a rope \<Rightarrow> nat" where
  "T_height_complete (RLeaf _ _) = 1" |
  "T_height_complete (RNode2 _ l _ _) = T_height_complete l + 1" |
  "T_height_complete (RNode3 _ l _ _ _ _) = T_height_complete l + 1"
                                                            
lemma T_height[simp]: "complete rs \<Longrightarrow> T_height_complete rs = height rs + 1" (* of by one case height leaf is defined as 0*)
  by (induction rs) auto                                 

(* We use T_height_complete here! *)
fun T_joinL :: "'a rope \<Rightarrow> 'a rope \<Rightarrow> nat" where
  "T_joinL l r = T_height_complete l + T_height_complete r + (
      if height l = height r then 1
      else (case r of
      RNode2 llenr lr rlenr rr \<Rightarrow> T_joinL l lr |
      RNode3 llenr lr mlenr mr rlenr rr \<Rightarrow> T_joinL l lr) + 1)"

(*
the joinL bound can be broken down into three parts.

- bound of the simplified version (T_joinL_simp): (height r - height l) + 1
- height l is called #(height difference) times: (height r - height l) * height l
- height r is called with decreasing parameter until height are the same:
    ((height r + 1 ) * (height r+2)) div 2 - (((height l) * (height l + 1)) div 2)
*)

(*
We have a detailed look at the last one in particular
*)

(* This timing function basically only simulates the calls to `height r` *)
fun T_height_only_right :: "'a rope \<Rightarrow> 'a rope \<Rightarrow> nat" where
  "T_height_only_right l r = T_height_complete r + (if height l = height r then 0 else  (case r of
      RNode2 llenr lr rlenr rr \<Rightarrow> T_height_only_right l lr |
      RNode3 llenr lr mlenr mr rlenr rr \<Rightarrow> T_height_only_right l lr))"

(* This (afaik) should be the exact timing. However, I couldn't figure out to prove it :( (in the rest amount of time I had) *)
lemma T_height_only_right_time:
  fixes l r :: "'a rope"
  assumes "height l < height r"
  assumes "complete l" "complete r"
  shows "T_height_only_right l r = ((height r + 1 ) * (height r+2)) div 2 - (((height l) * (height l + 1)) div 2)"
  using assms
  apply (induction r)
  (* apply auto *) (* There is one case missing to prove. something about height l probably! *)
  (* apply auto *)
  sorry

(* However, we can formulate this upper bound *)
lemma T_height_only_right_bound:
  fixes l r :: "'a rope"
  assumes "height l < height r"
  assumes "complete l" "complete r"
  shows "T_height_only_right l r \<le> ((height r + 1 ) * (height r+2)) div 2"
  using assms
  apply (induction r)
  apply auto
  done

(* So, it is quadratic in the height of r. *)
lemma T_height_only_right_bound_2:
  fixes l r :: "'a rope"
  assumes "height l < height r"
  assumes "complete l" "complete r"
  shows "T_height_only_right l r \<le> (height r + 1)^2"
  using assms
  apply (induction r)
  apply (auto simp: numeral_eq_Suc)
  done

(* This are all the three terms combined. What we would expect as an exact timing function. *)
lemma joinL_time:
  fixes l r :: "'a rope"
  assumes "height l < height r"
  assumes "complete l" "complete r"
  assumes "invar l" "invar r"
  shows "T_joinL l r = (height r - height l) + 1 + (height r - height l + 1) * (height l + 1) + ((height r + 1 ) * (height r+2)) div 2 - (((height l) * (height l + 1)) div 2)"
  using assms
  apply (induction r)
  (*apply auto*) (*Again runs forever and 2 goals to prove. probably rather hard. *)
  sorry

(*
(height r - height l) + 1 + (height r - height l + 1) * (height l + 1)
= (height r - height l + 1) * (height l + 2)
\<le> (height r + 1) * (height l + 2)
*)

(*
So this is our final joinL bound.
It's quadratic in the height of the tree.

Our main finding:
If it wouldn't be for the height calls (e.g. if we would track how many trees we would need to descend in the first call,
or would store the height information in the tree, we would have the bound of joinL_simp_bound, meaning
linear in the height difference between the two ropes.
*)
lemma joinL_bound[]:
  fixes l r :: "'a rope"
  assumes "height l < height r"
  assumes "complete l" "complete r"
  assumes "invar l" "invar r"
  shows "T_joinL l r \<le> 2* (height r + 1)^2"
  using assms
  apply (induction r)
  apply (auto simp: numeral_eq_Suc)
  done


(*
Now let's look at joinR both simp and normal:
*)

fun T_joinR_simp :: "'a rope \<Rightarrow> 'a rope \<Rightarrow> nat" where
  "T_joinR_simp l r = (
      if height l = height r then 1
      else (case l of
        RNode2 llenl ll rlenl rl \<Rightarrow> T_joinR_simp rl r |
        RNode3 llenl ll mlenl ml rlenl rl \<Rightarrow> T_joinR_simp rl r) + 1)"

fun T_joinR :: "'a rope \<Rightarrow> 'a rope \<Rightarrow> nat" where
  "T_joinR l r = T_height_complete l + T_height_complete r +(
      if height l = height r then 1
      else (case l of
        RNode2 llenl ll rlenl rl \<Rightarrow> T_joinR rl r |
        RNode3 llenl ll mlenl ml rlenl rl \<Rightarrow> T_joinR rl r) + 1)"

(* Both lemmas are dual *)

lemma joinR_simp_bound[]:
  fixes l r :: "'a rope"
  assumes "height l > height r"
  assumes "complete l" "complete r"
  assumes "invar l" "invar r"
  shows "T_joinR_simp l r \<le> height l + 1"
  using assms
  apply (induction l)
  apply auto
  done

lemma joinR_bound[]:
  fixes l r :: "'a rope"
  assumes "height l > height r"
  assumes "complete l" "complete r"
  assumes "invar l" "invar r"
  shows "T_joinR l r \<le> 2* (height l + 1)^2"
  using assms
  apply (induction l)
  apply (auto simp: numeral_eq_Suc)
  done


(* Now let's look at the final concat complexity *)

fun T_concat_simp :: "'a rope \<Rightarrow> 'a rope \<Rightarrow> nat" where
  "T_concat_simp l r = T_height_complete l + T_height_complete r + (case cmp (height l) (height r) of
    LT \<Rightarrow> T_joinL_simp l r |
    EQ \<Rightarrow> 1 |
    GT \<Rightarrow> T_joinR_simp l r)"

fun T_concat :: "'a rope \<Rightarrow> 'a rope \<Rightarrow> nat" where
  "T_concat l r = T_height_complete l + T_height_complete r + (case cmp (height l) (height r) of
    LT \<Rightarrow> T_joinL l r |
    EQ \<Rightarrow> 1 |
    GT \<Rightarrow> T_joinR l r)"

lemma concat_simp_bound:
  fixes l r :: "'a rope"
  assumes "complete l" "complete r"
  assumes "invar l" "invar r"
  shows "T_concat_simp l r \<le>  3 * (max (height l) (height r) + 1)"
  using assms joinR_simp_bound joinL_simp_bound
  apply (induction l r rule: T_concat_simp.induct)
  by fastforce


(*
2 * (max (height l) (height r) + 1) + 2* (height l + 1)^2 + 2* (height r + 1)^2
= 2 * (max (height l) (height r) + 1) + 4* (max (height l) (height r) + 1)^2
\<le> 4* (max (height l) (height r) + 2)^2
*)

lemma concat_bound_step:
  fixes l r :: "'a rope"
  assumes "complete l" "complete r"
  assumes "invar l" "invar r"
  shows "T_concat l r \<le>  4* (max (height l) (height r) + 2)^2"
  using assms joinR_bound joinL_bound
  apply (induction l r rule: T_concat_simp.induct)
  by (fastforce simp: numeral_eq_Suc)

(*
So two findings:
relying on a height function that is aware of complete trees yields a bound for concat that is
quadratic in the maximum height of the two ropes that get concatenated.

Would we eliminate the height comparison in each step (or assuming equal height ropes),
we get a time complexity that is linear in the height of the two trees (or more specifically linear
in the height difference of the two trees). This doesn't take into account the memory consumption
of the data structure.

Hope you liked it :)
*)

end