theory ch611
imports Main
begin

text{*A manual proof in set theory:*}

thm equalityI subsetI
thm UnI1 UnI2 UnE

lemma "A Un B = B Un A"
apply(rule equalityI)
 apply(rule subsetI)
 apply(erule UnE)
  apply(rule UnI2)
  apply(assumption)
 apply(rule UnI1)
 apply(assumption)
apply(rule subsetI)
apply(erule UnE)
 apply(rule UnI2)
 apply(assumption)
apply(rule UnI1)
apply(assumption)
done


text{* Most simple proofs in set theory are automatic: *}

lemma "-(A \<union> B) = (-A \<inter> -B)"
by(blast)

lemma "{x . P x \<and> Q x} = {x . P x} \<inter> {x. Q x}"
by(blast)

end