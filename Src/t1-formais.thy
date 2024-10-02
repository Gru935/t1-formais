theory "t1-formais"
  imports Main
begin

(*
  Integrantes:
  Arthur Both
  Gabriel Ferreira
  João Pedro Cunha
*)

primrec cat :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
 cat1:"cat [] l = l" |
 cat2:"cat (h # T) l = h # (cat T l)"

primrec tamanho :: "'a list \<Rightarrow> nat" where
  tamanho1:"tamanho [] = 0" |
  tamanho2:"tamanho (h # T) = 1 + tamanho T"

datatype 'a ArvBin = Vazia | Nodo "'a ArvBin" 'a "'a ArvBin"

primrec numnodos :: "'a ArvBin \<Rightarrow> nat" where
  numnodos1:"numnodos Vazia = 0" |
  numnodos2:"numnodos (Nodo L x R) = 1 + numnodos L + numnodos R"

primrec espelho :: "'a ArvBin \<Rightarrow> 'a ArvBin" where
  espelho1:"espelho Vazia = Vazia" |
  espelho2:"espelho (Nodo L x R) = Nodo (espelho R) x (espelho L)"

primrec conteudo :: "'a ArvBin \<Rightarrow> 'a list" where
  conteudo1:"conteudo Vazia = []" |
  conteudo2:"conteudo (Nodo L x R) = x # (cat (conteudo L) (conteudo R))"


(*Prova da propriedade 1*)

theorem tamanho_cat: "\<forall>L2 :: 'a list . tamanho (cat L1 L2) = tamanho L1 + tamanho L2"
proof (induction L1)
  show "\<forall>L2 :: 'a list . tamanho (cat [] L2) = tamanho [] + tamanho L2"
  proof (rule allI)
    fix L2::"'a list"
    have "tamanho (cat [] L2) = tamanho (L2)" by (simp only:cat1)
    also have "... = tamanho [] + tamanho L2" by (simp)
    finally show "tamanho (cat [] L2) = tamanho [] + tamanho L2" by (simp)
  qed
next
  fix h::'a and L1::"'a list"
  assume HI:"\<forall>L2 :: 'a list . tamanho (cat L1 L2) = tamanho L1 + tamanho L2"
  show "\<forall>L2 :: 'a list . tamanho (cat (h#L1) L2) = tamanho (h#L1) + tamanho L2"
  proof (rule allI)
    fix L2::"'a list"
    have "tamanho (cat (h#L1) L2) = tamanho (h#(cat L1 L2))" by (simp only:cat2)
    also have "... = 1 + tamanho(cat L1 L2)" by (simp only:tamanho2)
    also have "... = 1 + tamanho L1 + tamanho L2" by (simp only:HI)
    also have "... = tamanho (h#L1) + tamanho L2" by (simp only:tamanho2)
    finally show "tamanho (cat (h#L1) L2) = tamanho (h#L1) + tamanho L2" by (simp)
  qed
qed

(*Prova da propriedade 2*)

theorem numnodos_tamanho: "numnodos A = tamanho (conteudo A)"
proof (induct A)
  show "numnodos Vazia = tamanho (conteudo Vazia)"
  proof -
    have "numnodos Vazia = 0" by (simp only:numnodos1)
    also have "0 = tamanho []" by (simp only:tamanho1)
    also have "tamanho [] = tamanho (conteudo Vazia)" by (simp)
    finally show "numnodos Vazia = tamanho (conteudo Vazia)" by (simp)
  qed
next
  fix L::"'a ArvBin" and R::"'a ArvBin" and x::"'a"
  assume HI1:"numnodos L = tamanho (conteudo L)"
  assume HI2:"numnodos R = tamanho (conteudo R)"
  show "numnodos (Nodo L x R) = tamanho (conteudo (Nodo L x R))"
  proof -
    have "numnodos (Nodo L x R) = 1 + numnodos L + numnodos R" by (simp only:numnodos2)
    also have "... = 1 + tamanho (conteudo L) + numnodos R" by (simp only:HI1)
    also have "... = 1 + tamanho (conteudo L) + tamanho (conteudo R)" by (simp only:HI2)
    also have "... = 1 + tamanho (cat (conteudo L) (conteudo R))" by (simp only:tamanho_cat)
    also have "... = tamanho (x#(cat (conteudo L) (conteudo R)))" by (simp only:tamanho2)
    also have "... = tamanho (conteudo (Nodo L x R))" by (simp only:conteudo2)
    finally show "numnodos (Nodo L x R) = tamanho (conteudo (Nodo L x R))" by (simp)
  qed
qed

end