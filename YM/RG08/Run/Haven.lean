import YM.RG08.Run.Parts
/-!
# Pol filtration in projection report. True width on repeated D. Post on upgrades.
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
noncomputable section
namespace YM.RG08.Run
open Filter Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Reflect UVExt.Paths Work.F08 Push.AbsoluteSums
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Place Source Source.Drops Labels Summit Scores Door Pill
open scoped BigOperators Topology Real ContDiff
variable {X:Chain}{G:Gauge}{E e N r d τ D j t i k m l n s :ℕ}{R θ C w:ℝ}{F:Labels.Frame G d}{Ω:SectionData F}{ν:G.ColorIndex}{D':ChartRatio G}{H:Hol G}{P:KPrices X.kernel}{g:KGate P}{Q:Lending G X.kernel}{S:Prism G X.kernel g Q E}
variable {h:1/2≤R}{hD:d+1≤D} {T:Signals P Q E τ H Ω h hD}

section gates
-- program general before K named
variable {κ:KernelChoices}
structure Aperture (G:Gauge)(K:KPrices κ)(k E τ d D:ℕ)(R:ℝ) where
  gate : ℕ→ℕ -- independent
  policy i j (X:Flight i j) : 4 ≤ j→ d+2 ≤ i→gate i ≤ X.L.val → ∀ r≤τ+E, ∀ V:EnvelopeU D R G r, Polished V→ Abates V (d+1)→∀ A,cis k 1 V A→ cis k 1 (aboard d (eff κ X G) V) (A/Real.sqrt X.L.val)
  paper: 1/2 ≤ R
  test : d+1≤D
  budget: d*d*(τ+E) ≤ k -- projection exponent. state separately

private lemma onePolicy (G:Gauge)(K:KPrices κ) (d D r k i j:ℕ)(he:d+1≤k)(hD:d+1≤D)(h:1/2≤R): ∃ n:ℕ,∀ X:Flight i j,4 ≤ j→d+2≤ i→ n ≤ X.L.val→∀ V:EnvelopeU D R G r, Polished V→Abates V (d+1)→∀ A,cis k 1 V A → cis k 1 (aboard d (eff κ X G) V) (A/Real.sqrt X.L.val) := by
   obtain ⟨C,hC,H⟩:= pan (G:=G) he h hD (K.positive j) (K.solvent j) r
   obtain ⟨n,hN⟩:= exists_nat_gt (C^2)
   refine ⟨n,fun X hj hp hn V hv hx a hb=> Ink.raise (H X.L _ ?_ V hv hx a hb) ?_⟩
   · refine colorPay X _ ⟨X.odd,fun p he=> ?_⟩; have ht:= K.offers i j X p (by omega) hj; simpa only [Carrier.linesOf,Vale.height,div_eq_mul_inv,Nat.add_comm,inv_pow] using ht
   let a':=(X.L.val:ℝ); have hL:0<a':= by unfold a'; positivity
   have hr:0≤a:=hb.nonneg
   have he: 0<Real.sqrt a':= Real.sqrt_pos.2 hL
   have hq : C ≤ Real.sqrt a' := (pow_le_pow_iff_left₀ hC he.le (show 2≠0 by decide)).1 ((hN.le.trans (show (n:ℝ) ≤ a' from Nat.cast_le.mpr hn)).trans_eq (Real.sq_sqrt hL.le).symm)
   apply le_trans (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hq hL.le) hr) (le_of_eq ?_); change Real.sqrt a'/a'*a=_/Real.sqrt a'; field_simp
   rw [Real.sq_sqrt hL.le]
lemma prepareA (G:Gauge)(K:KPrices κ) (k E τ d D:ℕ)(he:d+1≤k)(hD:d+1≤D)(hk: d*d*(τ+E)≤ k)(h:1/2≤R): Nonempty (Aperture G K k E τ d D R):= by
   choose X H using fun r j i=> onePolicy G K d D r k i j he hD h
   let A i j:= (range (τ+E+1)).sup (fun r=>X r j i)
   refine ⟨⟨fun i=> max (A i i) (A i (i-1)),fun i j x hj hB hX r hr=> H r j i x hj hB ?_,h,hD,hk⟩⟩
   refine (le_sup (s:=range (τ+E+1)) (b:=r) (f:=fun r=>X r j i) (by simp; omega)).trans (le_trans ?_ hX)
   change A i j ≤ _; by_cases he:i=j
   · rw [he]; exact le_max_left ..
   have hx:i-1=j:=by have hh:=x.mono; have hz:=x.narrow; omega
   rw [hx]; exact le_max_right ..
variable {I:Type}{T':Aperture G P k E τ d D R}{u: I→Windows}
open Wings
structure Heirs (T: Aperture G P k E τ d D R)(u:I→Windows) : Prop where
  high (i:Launch u) : T.gate (X.J (i.i+1)) ≤ (X.S.block i.i).val
  ageL (i:Launch u): d+2 ≤ X.J (i.i+1)
lemma Heirs.contract (he:Heirs T' u)(t:Wings u 1)(V:EnvelopeU D R G r)(hb:Polished V)(hk:Abates V (d+1))(hv:r≤τ+E)(A:ℝ)(hV:cis k 1 V A): cis k 1 (aboard d (babyQ G X t) V) (A * gain X.S (1/2) t.i (t.i+1)):= by rw [gain_succ_half,mul_one_div]; exact T'.policy _ _ _ (X.adm _) (he.ageL _) (he.high _) _ hv V hb hk A hV
end gates

-- Project on any gauge-invariant kernel series.
section projection
variable (H:Hol G){Φ: ReadsU F D R}{U:BoardU D R G}
def eject (Φ:ReadsU F D R)(U:BoardU D R G):= U-edgeBook Φ (call H F U)
lemma edge_cost (h:Fits τ U)(ht:Boards Φ): Marvel τ (edgeBook Φ (call H F U)) ∧ Lank (edgeBook Φ (call H F U)) := by
   let S := call H F U
   constructor
   · refine across_b (V:=edgeBook Φ S) (fun i=> ⟨_,edge_marks Φ _ i,choir_array univ ?_⟩); intro a _
     refine choir_array (U:=fun j=> PowerSeries.coeff j (S a) • fem j (Φ a)) (range _) ?_; intro j _
     by_cases hv:slot a≤τ+j
     · exact choir_weight (stemmed (ht.rank a) hv) _
     unfold S call; rw [PowerSeries.coeff_mk,audit_cap H h _ (by omega),zero_smul]; exact choir_none
   intro e k; rw [edge_marks Φ S e e le_rfl]; exact (lank_tbl (fun i _=>lank_tbl (X:=fun j=>PowerSeries.coeff j (S i) • fem j (Φ i)) (fun _ _=> lank_wt (lank_fee (ht.paid i) _) _))) e k
lemma studyAll (hV: Genuine H Φ)(p: Native (Letter F)): call H F (edgeBook Φ p)=p:= by
   funext j; unfold call; rw [audit_funds H d _ _ (fun b=>wider (hV.rank b) (slot_le ..)) hV.paid]
   apply Eq.trans (sum_eq_single_of_mem j (mem_univ _) (fun i _ hi=>?_)); rotate_left
   · rw [show PowerSeries.mk _= _ from (show call H F (Φ i) j=0 by change atlas H Φ j i=0; rw [hV.cost,Matrix.one_apply,if_neg (Ne.symm hi)]),mul_zero]
   rw [show PowerSeries.mk _=_ from (show call H F (Φ j) j=1 by change atlas H Φ j j=1; rw [hV.cost,Matrix.one_apply,if_pos rfl]),mul_one]
structure Crop (τ:ℕ)(U:BoardU D R G)(H:Hol G)(F:Labels.Frame G d) : Prop where
   hU : Marvel τ U
   paid : Lank U
   spine : auditT H F U=0
lemma pin (h:Marvel τ U)(hp:Lank U)(he:Genuine H Φ) : Crop τ (eject H Φ U) H F:= by
  obtain ⟨hz,hV⟩:= edge_cost H h.cap he.toBoards; unfold eject; let A:=edgeBook Φ (call H F U); refine ⟨?_,?_,?_⟩
  · rw [sub_eq_add_neg,← neg_one_smul ℝ]; exact choir_plus h (choir_weight hz _)
  · rw [sub_eq_add_neg,← neg_one_smul ℝ]; exact lank_add hp (lank_wt hV _)
  rw [audit_sub H h hz hp hV, sub_eq_zero]; funext e v; have H' := congr_arg (PowerSeries.coeff e) (congr_fun (studyAll H he (call H F U)) v); unfold call at H'; simp_rw [PowerSeries.coeff_mk] at H'; exact H'.symm
end projection
end YM.RG08.Run
