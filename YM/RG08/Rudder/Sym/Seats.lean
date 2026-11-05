import YM.RG08.Rudder.Sym.Parasol

noncomputable section
namespace YM.RG08.Rudder.Symmetry
open scoped Topology BigOperators Classical ENNReal
open Forms Packets Finset Function Lattice Pert.Bulk Exterior Laurent AnalyticNext.QuarticMatch.BoxChain
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {I:Type}{n:ℕ}{F:Raw I n}{s:List (Fin n)}

lemma boundary_swap {j k:Fin n}:boundary j (boundary k F)=boundary k (boundary j F):=by
 ext x; exact congrFun (lower_switch k j (hum F (fun i=>(x i).2.2))) (fun i=>((x i).1,(x i).2.1)) -- lower_switch ? order
lemma perm_toll (ξ:Equiv.Perm (Fin n))(s:Signed){x:Tape n (Market (Tone I))}:levy s x=levy s (x ∘ ξ):= (Equiv.prod_comp ξ _).symm
lemma cardinal_perm (h:Cardinal F)(ξ:Equiv.Perm (Fin n)):Cardinal (woven F ξ):=by
 intro s;funext x;rw [orbit_apply,perm_toll ξ s]; exact congrFun (h s) (x ∘ ξ)
lemma boundary_perm (ξ:Equiv.Perm (Fin n))(i:Fin n):boundary (ξ i) (woven F ξ) = woven (boundary i F) ξ:=by
 ext x;change boundary _ _ x = boundary _ _ _; rw [chart,chart];refine sum_congr rfl fun k _=>?_
 unfold lifted woven;change (if _ then _ else _)=(if k∈(x (ξ i)).2.1 then _ else _);split_ifs;rfl
 have he(y):update x (ξ i) y ∘ ξ=update (x ∘ ξ) i y:=by funext a;rcases eq_or_ne a i with hh|hh <;> simp [hh, ξ.injective.eq_iff]
 simp only [he,comp_apply]
lemma patch_perm (ξ:Equiv.Perm (Fin n))(F:Raw I n): patchL (s.map ξ) (woven F ξ)=woven (patchL s F) ξ:=by
 induction s generalizing F with
 | nil=>rfl
 | cons i t ih=> change patchL (t.map ξ) (boundary (ξ i) (woven F ξ))= woven (patchL t (boundary i F)) ξ;rw [boundary_perm,ih]
lemma patch_comm {s t:List (Fin n)}(h:s.Perm t)(F:Raw I n):patchL s F=patchL t F:=by
 induction h generalizing F with
 | nil=>rfl
 | cons i _ ih=>exact ih (boundary i F)
 | swap i j t=>change patchL t (boundary _ (boundary _ F))=patchL t (boundary _ (boundary _ F));rw [boundary_swap]
 | trans _ _ h₁ h₂=>rw [h₁,h₂]
lemma picture_woven (ξ:Equiv.Perm (Fin n))(F:Raw I n):picture I n (woven F ξ)=woven (picture I n F) ξ:=by
 unfold picture;rw [←patch_perm];apply patch_comm
 apply (List.perm_ext_iff_of_nodup (List.nodup_finRange _) (List.Nodup.map ξ.injective (List.nodup_finRange _))).mpr
 intro a;simp only [List.mem_finRange,List.mem_map,true_and,true_iff]; exact ξ.surjective _
lemma picture_clean (F:Raw I n):picture I n (bleach F)=bleach (picture I n F):=by simp_rw [bleach,map_smul,map_sum,picture_woven]

lemma cardinal_clean {F:Raw I n}(h:Cardinal F):Cardinal (bleach F):=by intro s;unfold bleach;rw [map_smul,map_sum];simp_rw [show ∀ e:Equiv.Perm (Fin n),orbit s (woven F e)=woven F e from fun e=>cardinal_perm h e s]
lemma clean_field {F:Raw I n}{r:ℕ}(h:Graded F fun _=>r):Graded (bleach F) fun _=>r:= by
 rw [graded_iff] at *; intro i x hx; unfold bleach; rw [Pi.smul_apply,Finset.sum_apply,sum_eq_zero (fun e _=>?_),smul_zero]
 unfold woven; apply h (e.symm i); simpa only [comp_apply,Equiv.apply_symm_apply] using hx
end YM.RG08.Rudder.Symmetry
