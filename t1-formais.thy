theory "t1-formais"
  imports Main
begin

(*Integrantes:
  Arthur Both
  Gabriel Ferreira
  João Pedro Cunha
*)

fun cat :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "cat [] l = l" |
  "cat (h # T) l = h # (cat T l)"

fun tamanho :: "'a list \<Rightarrow> nat" where
  "tamanho [] = 0" |
  "tamanho (h # T) = 1 + tamanho T"

datatype 'a ArvBin = Vazia | Nodo "'a ArvBin" 'a "'a ArvBin"

fun numnodos :: "'a ArvBin \<Rightarrow> nat" where
  "numnodos Vazia = 0" |
  "numnodos (Nodo L x R) = 1 + numnodos L + numnodos R"

fun espelho :: "'a ArvBin \<Rightarrow> 'a ArvBin" where
  "espelho Vazia = Vazia" |
  "espelho (Nodo L x R) = Nodo (espelho R) x (espelho L)"

fun conteudo :: "'a ArvBin \<Rightarrow> 'a list" where
  "conteudo Vazia = []" |
  "conteudo (Nodo L x R) = x # (cat (conteudo L) (conteudo R))"


(*Prova da propriedade 1*)
theorem tamanho_cat: "tamanho (cat L1 L2) = tamanho L1 + tamanho L2"
  proof (induct L1)
  case Nil
  then show ?case by auto
next
  case (Cons h T)
  then show ?case by auto
qed

lemma tamanho_cat_example: "tamanho (cat [1, 2] [3, 4]) = tamanho [1, 2] + tamanho [3, 4]"
  by (simp add: tamanho_cat)


(*Prova da propriedade 2*)
lemma numnodos_tamanho_conteudo: "numnodos A = tamanho (conteudo A)"
  for A :: "'a ArvBin"
proof (induction A)
  case Vazia
  then show ?case by simp
next
  case (Nodo L x R)
  then show ?case
  proof -
    have "conteudo (Nodo L x R) = x # (cat (conteudo L) (conteudo R))"
      by simp

    have "tamanho (conteudo (Nodo L x R)) = 1 + tamanho (conteudo L) + tamanho (conteudo R)"
      by simp

    have "numnodos (Nodo L x R) = 1 + numnodos L + numnodos R"
      by simp

    (* Prova da relação entre o tamanho da concatenação e os tamanhos das partes *)
    have "tamanho (cat (conteudo L) (conteudo R)) = tamanho (conteudo L) + tamanho (conteudo R)"
    proof (induction "conteudo L" "conteudo R" rule: cat.induct)
      case (1 l)
      then show ?case by simp
    next
      case (2 h T l)
      then show ?case by simp
    qed

    (* Concluindo a prova *)
    have "numnodos (Nodo L x R) = 1 + (numnodos L + numnodos R)"
      by simp

    finally show ?case 
      by (simp add: Nodo.IH)
  qed
qed


end