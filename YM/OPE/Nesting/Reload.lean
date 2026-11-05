import YM.OPE.Nesting.Supplies

/-! Loading the next substitute through one high **finite** horizon in a
strict temporal sublayer (weights of all currently formed branches supplied
before the round). In a constant-rate ridge with no strict gap, just keep the
comparable alternatives.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Nesting
open Orbits Orbits.Reader Function Filter Extraction Set Table Tree Measures Menu Atom MeasureTheory
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{C:Family G}{F:Order}{S:Table C.book}(U:Spec.Final C F S)
  (R:Reader U.sector.derivatives U.sector.turns U.room.kernel.spin)
variable {L:Type}{t:Tree}{l:Filter L}{T:L→ℝ}{o:L→E4}{z:Tree.Envelope L t}
variable {κ b W r:ℝ}{a:t.Inner→ℝ} (v:t.Leaf→S.Tag)

def loadedRaw {t:Tree}(z:Tree.Envelope L t)(v:t.Leaf→S.Tag)(o:L→E4)(n:ℕ):Menu S L := Menu.through R n ((Menu.raw z v).pick ()) o
variable {Ω k:ℝ}(hd:Meets U R l T z (Tree.center z) k Ω (Menu.raw z v))(h:t.Regular l T κ a z)
-- syntax of h reversed `t.Regular`? resolves?
omit h
include hd in
lemma cost_loaded (hk:κ≤k) (m:ℕ):Comparable l T z κ Ω (loadedRaw U R z v (Tree.center z) m):=by
    have h₁(j:Cut R m):(loadedRaw U R z v (Tree.center z) m|>.pick j) = punctum (oneTag U R j.1 j.2) ((Menu.raw z v).charge R j.1 j.snd (Tree.center z)) (Tree.center z):=by
         exact congr_arg (fun p=> punctum (oneTag U R j.1 j.2) p (Tree.center z)) (funext fun q=> Eq.trans (one_mul (_:ℂ)) ((raw_charge z v R j.1 j.2 (Tree.center z) q).symm))
    intro j; change Cut R m at j; rw [h₁]
    refine ⟨⟨fun _=> t.topSeat,rfl⟩,Kept.sole l T (Tree.center z) κ, (hd.output j.1.val j.2).mono ?_⟩
    rw [punctum_cost]; exact sub_le_sub_left (mul_le_mul_of_nonneg_left hk j.1.val.cast_nonneg) _

lemma loaded_test {J:Type}[Fintype J]{m:ℕ}{w:J→S.Tag}{s:L→Viewers U}{y:L→J→E4}:∀ i, delta U R (Menu.raw z v) m (Tree.center z) s w y i=(Menu.raw z v).atView (spectator U ∘ s) y w i - (loadedRaw U R z v (Tree.center z) m).atView (spectator U ∘ s) y w i :=by
    intro i
    change _ - ∑ j:Cut R m,(Menu.raw z v).charge R j.1 j.2 (Tree.center z) i*_ = _ - (∑ j:Cut R m, ((loadedRaw U R z v (Tree.center z) m).pick j).sample (spectator U ∘ s) y w i)
    apply congr_arg (_-·) (Finset.sum_congr rfl fun j hj=>?_)
    rw [raw_charge]; change _ = (1:ℂ) * _ * _; rw [one_mul]
    rfl
include h
include hd in
lemma high (hk:t.topAge κ a=k)(hg:κ<k)(b₀:κ≤ b) (W r:ℝ)(D:ℕ) : ∃ H:ℕ, D ≤ H ∧ let P:=loadedRaw U R z v (Tree.center z) H; Comparable l T z κ Ω P ∧ Agrees U l T z κ b W r (Menu.raw z v) P :=by
     subst k; obtain ⟨N,hN⟩:=exists_nat_gt ((Ω+W*b-r)/(t.topAge κ a-κ)); let q:=max N D
     refine ⟨q,(le_max_right ..),cost_loaded U R v hd hg.le q, fun w y s he hu hb=> ?_⟩
     have hc:=h.zeroBorder
     apply (hd.tested w y q s b κ hb (interval_comp hu (fun _:Unit=>_) id) hu hc b₀ hg.le).mono ?_ |>.congr (Eventually.of_forall fun i=> loaded_test U R ..)
     rw [div_lt_iff₀ (sub_pos.mpr hg)] at hN; have hf₀:= mul_le_mul_of_nonneg_right (show (N:ℝ) ≤ ↑q + 1 from by exact_mod_cast le_max_left N D |>.trans q.le_succ) (sub_nonneg.mpr hg.le)
     linarith only [hf₀,hN,mul_le_mul_of_nonneg_right he (hc.trans b₀)]
end YM.OPE.Nesting
