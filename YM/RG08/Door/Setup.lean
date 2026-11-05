import YM.RG08.Door.Jasmine
/-!
# pre-block market. field horizon, actual test address, smoothing demands.
Preserves momentum buffers even with engineering mark rescalings. Off-diagonals at same
sector tick priced before scales. Joint counts explicit. -/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
noncomputable section
namespace YM.RG08.Door
open Filter Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Staffer Reflect UVExt.Paths Work.F08 Push.AbsoluteSums
open Quire Shade Loom Vale Needle Tall PowerSeries Planned.PrimaryIntegral295 Place Source Source.Drops Labels
open scoped BigOperators Topology Real -- not Classical
variable {K : KernelChoices}{G : Gauge} {i k d t r j D:ℕ} (s : ℝ){F : Labels.Frame G d}{T:SectionData F}(H:Hol G)(h:T.Sound H)(hB:Bid.pop T) {R w v A B Z C:ℝ} {P:KPrices K}{Q:Lending G K}
-- stands = height pre calls INCLUDING weight price for leading T-inverse same-slot projections. `extra` Q ≥ 1 before widths. shelf.

abbrev eff (K : KernelChoices)(X:Flight j i)(G:Gauge):=painted G (Carrier.linesOf X K.penalty)
include h hB
lemma paidM (hx:1/2≤R)(hp:d+1≤D) : ∃ A:ℝ,1≤A ∧ ∀ (X:Flight j i),4≤ i → d+2≤j→ ∀ b v:Letter F, slot b=slot v→‖leadingV H T (d.le_succ.trans hp) hx X K.penalty b v‖≤ A * ((X.L.val:ℝ)^(d-fee b)) := by
  classical
  have hi (b v:Letter F) : ∃ A:ℝ,1≤A ∧ ∀ (X:Flight j i), 4≤ i → d+2≤j→slot b=slot v→ ‖leadingV H T (d.le_succ.trans hp) hx X K.penalty b v‖≤ A*((X.L.val:ℝ)^(d-fee b)) := by
    by_cases hb:4≤ i ∧ 4≤j∧ d+2≤j ∧ slot b=slot v
    · obtain ⟨hi,hj,hc,hv⟩:=hb; obtain ⟨A,hA,H⟩:= leading_in H h hB hx K.penalty_pos hi hj hc hp b v hv; exact ⟨A,hA,fun X _ _ _=> H X⟩
    exact ⟨1,le_rfl,fun X hi h hx=> (hb ⟨hi,hi.trans X.mono,h,hx⟩).elim⟩
  choose a ha H using hi
  let M:= ∑ p:Letter F × Letter F,a p.1 p.2; have hp'(b:Letter F×Letter F):0≤ a b.1 b.2:=zero_le_one.trans (ha ..); have he:0≤M:=sum_nonneg fun i _=>hp' i; refine ⟨1+M,le_add_of_nonneg_right he,fun X hi h b v hx=> ?_⟩
  exact (H b v X hi h hx).trans (mul_le_mul_of_nonneg_right ((single_le_sum (f:=fun (i:Letter F×Letter F)=>a i.1 i.2) (fun i _=> hp' i) (mem_univ (b,v))).trans (le_add_of_nonneg_left zero_le_one)) (by positivity))

lemma billsSl (hx:1/2≤R) (hp:d+1≤D) : ∃ A:ℝ,1≤A ∧ ∀ X:Flight j i, 4≤ i → d+2≤j→∀ U:Session (Letter F),Flash X.L U → (∀ b v:Letter F,slot b=slot v→ hot U 0 v b=leadingV H T (d.le_succ.trans hp) hx X K.penalty b v) →
    ∀ b v,‖diagonalSl (hot U⁻¹ 0) b v‖≤ A := by
  obtain ⟨M,hM,H⟩:=paidM (K:=K) (j:=j) (i:=i) H h hB hx hp
  let Q:=∑ k∈range (insolent F),(Fintype.card (Letter F)*(M+1))^k; have hp:0≤Q:=sum_nonneg fun i _=> pow_nonneg (by positivity) _; refine ⟨1+Q,le_add_of_nonneg_right hp,fun X hi hj U hU hv a b=>?_⟩ -- Plate equality
  unfold diagonalSl; change ‖if _ then Needle.hot U⁻¹ 0 a b else (0:ℝ)‖ ≤ _; split; next he=>
    exact (wingTips hU (fun i j he=> by rw [hv j i he.symm]; exact H X hi hj j i he.symm) (zero_le_one.trans hM) a b he).trans (le_add_of_nonneg_left zero_le_one)
  rw [norm_zero]; exact add_nonneg zero_le_one hp
omit h hB

lemma manExp (hx:1/2≤R)(hD:d+1≤D)(hs: 0<w)(he:0<B) (hp: B ≤ P.b i) (hz:1≤Z)(r:ℕ) : ∃ n:ℕ,∀ (X:Flight j i), 4≤ i → d+2≤j → n ≤ X.L.val → ∀ (V:EnvelopeU D R G r), Polished V→Abates V (d+1)→ ∀ C:ℝ,Quire.Lit V w C → Quire.Lit (aboard d (eff K X G) V) B (C/ Real.sqrt X.L.val/Z) := by
  obtain ⟨F,hF,HF⟩:= Vale.expGrowth (α:=Loc G 1) (β:=Loc G 1) d hs he hp (P.solvent _)
  obtain ⟨A,hA,H⟩:= Vale.sail_gain_l (F:=plyH w (α:=Loc G 1)) hx hF (plyH_one (α:=Loc G 1) he.le) hD r
  obtain ⟨n,hn⟩:= exists_nat_gt (max ((B*2)/w) ((Z*A)^2)); refine ⟨n,fun X hi hB h V hV ht C hC=>?_⟩
  have hQ : PaysPath (eff K X G) (P.b i) (P.bill i) d := colorPay X _ ⟨X.odd,fun k hk=> by
    have hP:= P.offers j i X k (by omega) hi
    unfold Carrier.linesOf; simpa only [Vale.height,Nat.add_comm,div_eq_mul_inv,inv_pow] using hP⟩ -- proof
  have he' : max _ _ ≤ (X.L.val:ℝ):= hn.le.trans (by exact_mod_cast h)
  have hh := H _ _ X.odd (HF _ _ (by apply (le_div_iff₀ (by norm_num)).mpr; exact (div_le_iff₀ hs).1 ((le_max_left ..).trans he')) hQ) V hV ht C (by
    rw [show brocade (plyH w)= (ling w:Beads (Loc G 1) r→ℝ) from funext fun i=>(bro_lit w i).symm]; exact hC) d
  have hE : (Z*A)^2 ≤ (X.L.val:ℝ) := (le_max_right ..).trans he'
  let a:= (X.L.val:ℝ); have hL:0<a:= by unfold a; positivity
  have hv:0<Real.sqrt a:=Real.sqrt_pos.2 hL
  have hb: Z*A ≤ Real.sqrt a:=(pow_le_pow_iff_left₀ (by positivity) hv.le (show 2≠0 by decide)).1 (by rw [Real.sq_sqrt hL.le]; exact hE)
  rw [show brocade (plyH B)= (ling B:Beads (Loc G 1) r→ℝ) from funext fun i=>(bro_lit B i).symm] at hh
  apply Ink.raise hh
  have hp:C≥0:=hC.nonneg
  refine (le_div_iff₀ (lt_of_lt_of_le zero_lt_one hz)).2 ((le_div_iff₀ hv).2 ?_)
  calc
    _ = Z*A*(C/a)*Real.sqrt a := by unfold Vale.height a; rw [inv_pow,pow_succ]; field_simp
    _ ≤ Real.sqrt a*(C/a)*Real.sqrt a:=by gcongr
    _ = C := by field_simp; rw [Real.sq_sqrt hL.le]; ring
end YM.RG08.Door
