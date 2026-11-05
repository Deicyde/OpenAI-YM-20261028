import YM.RG08.Town.Rheum
/-!
# Scalar coefficients: diagonal and rough fee books. Work in same-reference native $
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.RG08.Town
open Filter Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Reflect Work.F08 Push.AbsoluteSums Matrix
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Place Source Source.Drops Labels Summit Scores Door Run Staffer PertExtension.Series.Radial PertExtension.Series.Tested
open scoped BigOperators Topology Real ContDiff Classical Matrix.Norms.Frobenius
variable {I J:Type}{p:Side}{n r k j e D h τ E ε:ℕ}{x:Cover}{θ A R σ:ℝ}{G:Gauge}
section frame
variable {L:I→Side}{y v w δ ρ η:I→ℝ}{K M : ∀ i,StripU G (L i)}{U A: I→ Tale G}{z : ∀ i:I,Site (L i)}
lemma lot_cis (h:Card k y ρ (fun i:I=>U i e r) w)(he:0≤v)(hx:v≤1)(hk:∀ i,v i/(L i).val≤ w i)(hp:Weighed y (fun i=> ((L i).val:ℝ)))(hz:Audience y): Card k y ρ (fun i=>reachP (z i) (U i) e r) v := by
  obtain ⟨B,hB,H⟩:=h.money; have he':0 ≤ Run.utter k 1:= utter_pos one_pos
  refine ⟨_, (((fiscal_lot (G:=G) hp hz).powers r).times (Weighed.constant y (show 0≤ (Run.utter k 1)^r by positivity))).times ((Weighed.constant y (show 0≤(1+4*(r:ℝ))^k by positivity)).times hB),fun i=> ?_⟩
  have h':= stage_l (plank_m (z i) (H i) (he i) (hx i) (hk i)) (he i) (hx i) one_pos (Q:=fun _=>skylight (Co (L i) (Loc G 1)) (Loc G 1)) (fun _=> skylight_price) (fun _=> zero_le_one)
  simpa only [prod_const_one,mul_one,mul_assoc,Pi.mul_apply] using! sew_cis h' (he i)
lemma lots (h:Drum k y δ ρ (fun i=>U i e r) (fun i=>A i e r) w)(he:0≤v)(hx:v≤1)(hk:∀ i,v i/(L i).val≤w i)(hp:Weighed y (fun i=> ((L i).val:ℝ)))(hz:Audience y) : Drum k y δ ρ (fun i=> reachP (z i) (U i) e r) (fun i=> reachP (z i) (A i) e r) v:= by
  have hv : 0≤w:=fun i=>(div_nonneg (he i) (by positivity)).trans (hk i)
  refine ⟨lot_cis h.first he hx hk hp hz,lot_cis h.second he hx hk hp hz,?_⟩
  rw [show _-_ =(fun i=>reachP (z i) ((U-A) i) e r) from funext fun i=>?_]; · exact lot_cis h.funds he hx hk hp hz
  have hh:=h.first.even hv i; have hA:=h.second.even hv i; unfold reachP lotS shiftP; simp only [Pi.sub_apply]; rw [Pens.tub_sub _ (show Pens (U i e r) from hh) (show Pens (A i e r) from hA)]; exact (spring_sub (hh.pours _) (hA.pours _) skylight_ok).symm -- binder

lemma hold_taps (h:LensP k E τ y δ η K M)(hx:Drum k y δ ρ (fun i=> U i e r) (fun i=>A i e r) w)(ht:0≤v)(hv:v≤1)(hh:∀ i, v i/(L i).val≤w i) : Drum k y δ ρ (fun i=>holdP (z i) (K i).tree (U i e r)) (fun i=>holdP (z i) (M i).tree (A i e r)) v := marks_pair (lots hx ht hv hh h.pay h.age) ht hv h.pos (Weighed.constant _ (Nat.cast_nonneg (Fintype.card (Loc G 1)))) h.owns h.age (scanned_contract h.meanT le_rfl h.age h.rent) h.rent
lemma rampart (h:LensP k E τ y δ η K M)(he: e ≤ E)(hq: ε≤τ)(ht:0≤v)(hv:v≤1)(hk:∀ i, v i/(L i).val≤w i) (hU:∀ i, Stone ε (U i))(hA:∀ i,Stone ε (A i))(hx:∀ i j, awaits 1 e r i j → Drum k y δ ρ (fun x=> U x i j) (fun x=> A x i j) w) : Drum k y δ ρ (fun i=> rampP ε (K i) (z i) (U i) e r) (fun i=> rampP ε (M i) (z i) (A i) e r) v:= by
   simp_rw [fun i=>holdsP (z i) (hU i) (h.one i),fun i=>holdsP (z i) (hA i) (h.two i)]
   apply marks_pair _ ht hv h.pos (Weighed.constant _ (Nat.cast_nonneg (Fintype.card (Loc G 1)))) h.owns h.age (scanned_contract h.meanT le_rfl h.age h.rent) h.rent
   let p S F j i:=murmur none (veiled ((S:∀ i:I, StripU G (L i)) i).cv) (S i).song (reachP (z i) ((F:I→Tale G) i)) (j+1) e r
   refine Drum.group (range (windows ε e)) h.age ht (F:=p K U) (H:=p M A) ?_; intro j hj
   let P:=veil_contract h.art h.rent
   refine aurora h.age h.pos h.rent P (fun i=>(h.one i).lived) (fun i=>(h.two i).lived) (fun i=> (reaches (hU i).cap (hU i).tidy (z i)).2) (fun i=> (reaches (hA i).cap (hA i).tidy (z i)).2) (fun i=>(h.one i).tune) (fun i=>(h.two i).tune) (fun m hm k hk u=> h.chargesG _ (hk.trans he) _ (by have hb:=mem_range.mp hj; unfold windows at *; omega) u) ht hv h.owns (fun i j' h'=>?_)
   exact lots (hx i j' (by simpa only [awaits,one_ne_zero,Nat.add_one_ne_zero,↓reduceIte] using h')) ht hv hk h.pay h.age
lemma spire_b (he:LensP k E τ y δ η K M)(hp:e≤E)(h:ε ≤ τ)(ht:0≤v)(hv:v≤1)(hk:∀ i, v i/(L i).val≤ w i)(hU:∀ i,Stone ε (U i))(hA:∀ i,Stone ε (A i))(hz:∀ i j, awaits 0 e r i j → Drum k y δ ρ (fun x=> U x i j) (fun x=> A x i j) w) : Drum k y δ ρ (fun i=>originS ε (K i) (z i) (U i) none e r) (fun i=>originS ε (M i) (z i) (A i) none e r) v:= by
    let p S P i:=originS ε ((S:∀ i:I,StripU G (L i)) i) (z i) ((P:I→Tale G) i) none e r
    have ht':= rampart (z:=z) he hp h ht hv hk hU hA (r:=r) (fun i j h=>hz i j (by unfold awaits at *; split_ifs at * <;> omega)); let Z := hold_taps (z:=z) he (hz e r (by simp [awaits])) ht hv hk
    have hb (K:∀ i,StripU G (L i))(U:I→Tale G) : p K U = (fun i=>rampP ε (K i) (z i) (U i) e r)+(fun i=>holdP (z i) (K i).tree (U i e r)):= funext fun i=>(sub_add_cancel ..).symm
    change Drum k y δ ρ (p K U) (p M A) v; rw [hb,hb]; exact ht'.more Z ht he.age
lemma core_b (he: LensP k E τ y δ η K M)(hp: e≤E)(h:ε≤τ)(ht:0≤v)(hv:v≤1)(hk:∀ i,v i/(L i).val≤ w i)(ho:0≤ρ)(hU:∀ i, Stone ε (U i))(hA:∀ i, Stone ε (A i))(hh:∀ i j, awaits 1 e r i j → Drum k y δ ρ (fun x=> U x i j) (fun x=> A x i j) w) : Drum k y δ ρ (fun i=> coreT ε (K i) (z i) (U i) e r) (fun i=>coreT ε (M i) (z i) (A i) e r) v := by
    have hz:= rampart (z:=z) he hp h ht hv hk hU hA hh
    simp_rw [fun i=> core_read (z i) (τ:=ε) (U i) (he.one i), fun i=> core_read (z i) (τ:=ε) (A i) (he.two i)] -- simp hash
    refine hz.more (A:=fun i=> _) (B:=fun i=> _) (Drum.group _ he.age ht (F:=fun j i=> glaze (K i).scale r j (e-j) • _) (H:=fun j i=> glaze (M i).scale r j (e-j) • _) ?_) ht he.age
    intro b hb; have ht':=mem_range.mp hb
    exact Drum.sc (spire_b (z:=z) he (by omega:b≤E) h ht hv hk hU hA (fun i j h'=>hh _ _ (Or.inl (by unfold awaits at h'; omega)))) (rehearseT he.age (e:=e-b) (fun i hi=>he.scaleT i (by omega)) (fun i=>(he.one i).once) (fun i=>(he.two i).once) _ _) ho he.age ht
end frame
section gears
-- Price in repeated unchanged rank before L. Smooth quadratic on chosen authorized stages.
variable {K:KernelChoices}(P:KPrices K)(G:Gauge)
include P
lemma sells_k (i j k r:ℕ)(h:r≠0): ∃ M:ℕ,∀ X:Flight i j,4≤ j → M ≤ X.L.val→∀ (p:Site X.L)(V:Rooted ℝ (Loc G 1) r), Tidy V→∀ A η γ,cis k η V A→0 ≤ γ → γ ≤1→ γ/X.L.val≤ η → cis k γ (holdP p (eff K X G) V) (A/ Real.sqrt X.L.val) := by
   let b := Run.utter k (P.b j)*(Fintype.card (Loc G 1)* P.bill j); let u:=(1+4*(r:ℝ))^k*b^r
   have hb: 0≤ b:= mul_nonneg (utter_pos (P.positive _)) (mul_nonneg (Nat.cast_nonneg _) (P.solvent _)); have hu:0≤u:= by unfold u; positivity
   obtain ⟨M,hM⟩:= exists_nat_gt (u^2); refine ⟨M,fun X hj hx p V hV A η γ hX hp ht hv=>?_⟩
   have hh: PaysPath (eff K X G) (P.b j) (P.bill j) 0:= colorPay X _ ⟨X.odd,fun v he=> ?_⟩; swap; · have hp:=P.offers i j X v (by omega) hj; simpa only [Carrier.linesOf,Vale.height,Nat.add_comm,div_eq_mul_inv,inv_pow] using hp
   let B:=(X.L.val:ℝ); have hQ: 1≤B:= by unfold B; exact_mod_cast X.L.property
   have hD:0 <B:=zero_lt_one.trans_le hQ
   have hh : (eff K X G).strip (P.b j) (P.bill j* B⁻¹):= by simpa [Carrier.linesOf,Vale.height,advanceC, B] using hh.offsets [] (show 0≤0 from le_rfl)
   have hr: Whole (eff K X G):=⟨_,_,P.positive _,hh⟩; have htA:=hX.nonneg; rw [belly_hold p hV hr]; apply Ink.raise (belly_exp_l p hX hh (P.positive _) (mul_nonneg (P.solvent _) (inv_nonneg.mpr hD.le)) hp ht hv)
   have hM:=hM.le.trans (show (_:ℝ) ≤ B from (by exact Nat.cast_le.mpr hx))
   have hT : u ≤ Real.sqrt B := (pow_le_pow_iff_left₀ hu (by positivity) (show 2≠0 by decide)).mp (by rw [Real.sq_sqrt hD.le]; exact hM)
   have hz : B ≤ B^r:= (pow_one B).symm.trans_le (pow_le_pow_right₀ hQ (Nat.one_le_iff_ne_zero.2 h))
   calc
     _ = u/B^r * A := by unfold u b; simp only [← mul_assoc,mul_pow,div_eq_mul_inv,inv_pow]
     _ ≤ Real.sqrt B/B * A:= by gcongr
     _ = _:= by change _ = A /Real.sqrt B; field_simp; rw [Real.sq_sqrt hD.le]
omit P in
structure Grotto (P:KPrices K) (k E τ:ℕ) where -- variables must explicit
   gate : ℕ→ℕ
   receipt i j k' r (X:Flight i j) : k'=k → r≠0 → r ≤ τ+E → 4 ≤ j→ gate i ≤ X.L.val→∀ (p:Site X.L) (V:Rooted ℝ (Loc G 1) r), Tidy V→∀ A η γ,cis k η V A→0≤γ→γ≤1→γ/X.L.val≤η→cis k γ (holdP p (eff K X G) V) (A/Real.sqrt X.L.val)
theorem bears (k τ E:ℕ): Nonempty (Grotto G P k E τ):= by
   choose T h using fun i j r=> sells_k P G i j k (r+1) (by omega)
   let W i j:= (range (τ+E)).sup fun r=> T i j r
   refine ⟨⟨fun i=>max (W i i) (W i (i-1)),fun i j _ r X _ hr he hP hx=>?_⟩⟩
   cases r with | zero=> contradiction | succ r=>
   refine h i j r X hP (le_trans (le_trans (Finset.le_sup (f:=fun r=>T i j r) (mem_range.mpr (by omega))) (show W i j≤ max _ _ from ?_)) hx); by_cases hp: i=j
   · rw [show j=i from hp.symm]; exact le_max_left ..
   rw [show i-1=j by have he:=X.mono; have hx:=X.narrow; omega]; exact le_max_right ..
end gears
end YM.RG08.Town
