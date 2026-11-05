import YM.UVExtension.Free.Lifts

/-! Convergence of crossed response (A, T) on the same histories. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Free
open Filter Function Lattice Laurent Bloch Metric Exterior Matrix Precision RG Next.Free Craft
open scoped Topology BigOperators Classical
variable {G : Gauge} (A : Levels G) (i : ℕ)

section ray
variable (k : ℝ) (hk : 0<k) (p : Momentum) (hp : p∈baseCube) (hn : p≠0)
local notation "L" => A.S.block i
local notation "P(" n ")" => destination A n i
include hk hp hn
open Flight

lemma tab_history : Arrives (fun n=> ((P(n)).tabE k p)⁻¹) := by
  let a : ℕ→Axis→Site L→ℂ:= fun n j l => scaleD L k (P(n)).wing (aliasAt p l) j
  let Y (l : Site L):= yen (massFilter (P(0)).patch) (aliasAt p l)
  have hy l:(aliasAt p l)∈baseCube ∧ aliasAt p l ≠ 0:= ⟨alias_base hp l (A.S.block_odd _), (alias_regular (P:=P(0)) (base_subset_realCube zone_pos hp) l (Or.inr hn)).2⟩
  have ha l j : Arrives (fun n=> a n j l):=
    (Arrives.steady ((((A.S.block i).val:ℂ)^2)⁻¹)).times (levelD_history A k _ (i+1) _ (hy l).1 (hy l).2)
  let U n l:= Y l*(∑ j,a n j l)
  have he : Arrives fun n=> ∑ l : Site L,U n l := Arrives.sum _ fun l _=> (Arrives.steady (Y l)).times (Arrives.sum _ fun j _=> ha l j)
  change Arrives fun n=> (∑ l : Site L,U n l)⁻¹; apply he.reci
  have hS l : Silver (Y l):= (P(0)).filter_silver (alias_real hp.1 _)
  have hP : 0 < (Y 0).re := by
    have ht := base_subset_realCube zone_pos hp
    apply (hS 0).re_ne (mul_ne_zero (mass_filter_live (P(0)) ht) ?_)
    have hh := mass_filter_live (P(0)) (realCube_neg ht)
    erw [(show aliasAt (-p) (0:Site L) = -aliasAt p (0:Site L) from by simpa only [neg_zero] using alias_reverse p (A.S.block_odd i) (0:Site L))] at hh
    exact hh
  let q := aliasAt p (0:Site L)
  let g := ‖((((A.S.block i).val:ℂ)^2)⁻¹)‖; have hg : 0<g:=norm_pos_iff.mpr (inv_ne_zero (pow_ne_zero _ (side_ne L)))
  obtain ⟨c,hc,hF⟩:= levelD_floor A k hk (i+1) q (hy 0).1 (hy 0).2 0
  have hv n j l: Silver (a n j l):=((Silver.side _).pow _).inv.mul (Train.D_cost _ hk _ _ (hy l).1.1)
  have hU n l : Silver (U n l) := (hS l).mul (Silver.sum _ _ fun j _=>hv n j l)
  refine ⟨(Y 0).re*(g*c),mul_pos hP (mul_pos hg hc), Eventually.of_forall fun j=>?_⟩
  have hz : g*c ≤ (a j 0 0).re := by
    rw [← (hv ..).norm]; change g*c ≤ ‖_ * ((location A j (i+1)).levelD k 0 q)‖; rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hF _) hg.le
  apply le_trans _ (Complex.re_le_norm (∑ l,U j l)); rw [Complex.re_sum]
  refine le_trans (b:=(U j 0).re) ?_ (Finset.single_le_sum (f:=fun l=> (U j l).re) (fun l _=> (hU j l).re_nonneg) (Finset.mem_univ _))
  unfold U; rw [(hS 0).real_mul,Complex.re_sum]
  exact mul_le_mul_of_nonneg_left (hz.trans (Finset.single_le_sum (f:=fun s=> (a j s 0).re) (fun s _=> (hv j s 0).re_nonneg) (Finset.mem_univ _))) hP.le

private lemma rotor_cloud : Arrives (fun n=> rotor 1 k (P(n)).land p) ∧
    Arrives (fun n=> pipe 1 k (P(n)).land p) ∧
    Arrives (fun n=> (P(n)).cloud k p) ∧ Arrives (fun n=> scaleR 1 k (P(n)).land p) := by
  let X n:=location A n i
  have h n : i<n→ X n=(P(n)).land:= loc_land A n i
  have hA (j):=levelD_history A k j i p hp hn
  have hh := (colors A k hk i p hp hn).1
  have hh' : Arrives fun n=> rotor 1 k (X n) p:= matprod (matprod (Arrives.steady _) hh) (Arrives.steady _)
  have ha:=rho_arrives A k hk i p hp hn
  obtain ⟨c,hc,hC⟩:=rho_floor A k hk i p hp hn
  have hE : Arrives (fun n=> (scaleR 1 k (X n) p)⁻¹):=by
    have hu:=ha.reci ⟨c,hc,Eventually.of_forall hC⟩; unfold scaleR; simp; exact hu
  have ht: Arrives (fun n=> fieldI 1 k (X n) p):= mask_arrives _ fun i'=> by
    simp only [scaleD_one]; obtain ⟨a,b,hA⟩:=levelD_floor A k hk i p hp hn i'
    exact (‹∀ j,Arrives _› _).reci ⟨a,b,Eventually.of_forall hA⟩
  have hT: Arrives fun n=> pipe 1 k (X n) p:=by
    obtain ⟨v,hv⟩:= matprod (Arrives.steady (mirage 1 0 p)) ht; obtain ⟨u,hu⟩:=hE; exact ⟨_, hu.smul hv⟩
  have hW:= matprod (matprod (matprod hh (Arrives.steady (signal 1 1 p))) (show Arrives fun n=> fieldD 1 k (X n) p from
    mask_arrives 1 (fun j=> by simp only [scaleD_one]; exact hA j))) (Arrives.steady (mirage 1 1 p))
  have he : ∀ᶠ n in atTop, X n=(P(n)).land:= (eventually_gt_atTop _).mono h
  refine ⟨hh'.copy (he.mono fun i hi=> by dsimp only; rw [hi]),hT.copy (he.mono fun i hi=> by dsimp only; rw [hi]),
      ?_,ha.copy (he.mono fun n hi=> ?_)⟩
  · refine hW.copy (he.mono fun n hi=>?_)
    change pulse k (X n) p * _ * fieldD 1 k (X n) p * _=pulse k _ p * _ * fieldD _ _ _ _ * _
    rw [hi]
  change (X n).rho k p=((↑(1:Side).val:ℂ)^4) *(P(n)).land.rho k p; rw [hi]; simp

lemma duo_history (l : Site (A.S.block i)) :
    Arrives (fun n:ℕ=> let V:=destination A n i; V.pilot k p l) ∧ Arrives (fun n:ℕ=>let V:=destination A n i; V.wire k p l):=by
  let q:=aliasAt p l
  let E:= (P(0))
  have hb : q∈baseCube := alias_base hp l (A.S.block_odd _); have he:=base_subset_realCube zone_pos hp
  have hq:q≠0:= (alias_regular (P:=E) he l (Or.inr hn)).2
  simp only [pilot_match k hk _ he hn,wire_match k hk _ he hn]
  have ht j : Arrives fun n=> scaleD L k (P(n)).wing q j:=(Arrives.steady _).times (levelD_history A k j (i+1) _ hb hq)
  obtain ⟨hR,hP,hC,hZ⟩:= rotor_cloud A i k hk p hp hn
  have hD:=mask_arrives 1 ht
  have hg : Arrives fun n=> weightsE k (P(n)) p q:=by
    unfold weightsE; simp_rw [div_eq_mul_inv]; exact ((Arrives.steady (massFilter (P(0)).patch (-q))).times (Arrives.sum _ (fun j _=> ht j))).times (tab_history A i k hk p hp hn)
  have hF: Arrives fun n=> (scaleR L k (P(n)).wing q)⁻¹:=by
    unfold scaleR; simp only [_root_.mul_inv_rev]; obtain ⟨v,hv,H⟩:=rho_floor A k hk (i+1) q hb hq
    exact ((rho_arrives A k hk _ q hb hq).reci ⟨v,hv,Eventually.of_forall H⟩).times (Arrives.steady _)
  have hm : Arrives fun n=> chainY k (P(n)) p q:=by
    unfold chainY; simp_rw [div_eq_mul_inv]; exact ((Arrives.steady (yen (massFilter E.patch) q)).times hZ).times hF
  constructor
  · apply (matprod (matprod (x:=fun n=> fieldD L k (P(n)).wing q) hD (Arrives.steady (flux E 1 q))) hR).plus
    obtain ⟨a,ha⟩:=hg; obtain ⟨b,hb⟩:= matprod (Arrives.steady (signal L 0 q)) hP; exact ⟨_,ha.smul hb⟩
  · apply (matprod (matprod (matprod (matprod ((colors A k hk (i+1) q hb hq).1) (Arrives.steady (signal L 1 q))) (y:=fun n=> fieldD L k (P(n)).wing q) hD) (Arrives.steady (flux E 1 q))) (Arrives.steady (mirage 1 1 p))).plus
    obtain ⟨a,ha⟩:=hm; obtain ⟨b,hb⟩:= hC; exact ⟨_,ha.smul ((show Continuous (fun x : Frequency 2 2 => flux E 2 q * (1-x)) from (by fun_prop)).continuousAt.tendsto.comp hb)⟩
omit hk hn

variable {m n : Type} [Fintype m] [Fintype n] (f:Thread (A.clock.J (i+1)) (A.clock.J i) m n) (e: ℕ) (h : Secured f)
include h
lemma issuing (ht : ∀ l : Site (A.S.block i), Arrives fun j=> f (destination A j i) p l):
    Arrives fun j:ℕ=> let g:Cross L m n:=meshBook f e [] (destination A j i); g.read p := by
  have hx (x : Site L): Arrives fun j=> spread f e [] (P(j)) x p := Arrives.sum (Finset.univ (α:= Site L)) (fun l _=> by
    obtain ⟨a,h⟩:= ht l; exact ⟨_, (h.const_smul (toll (A.S.block i) e * listChip (aliasAt p l) [])).const_smul (mode (aliasAt p l) (lift x))⟩)
  apply Arrives.columns; intro ⟨x,b⟩; apply Arrives.columns; intro a
  obtain ⟨Z,hZ⟩:= hx x
  refine Arrives.copy (f:=fun j=> spread f e [] (P(j)) x p b a) ⟨_,tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hZ _) _⟩
    (Eventually.of_forall fun i_dummy=>?_)
  change _ = (meshBook f e [] (P(i_dummy))).read p (x,b) a
  apply Eq.symm; exact h.bankRead (A.clock.adm (i+1)) e (u:=[]) (Nat.zero_le _) (P(i_dummy)) x hp b a
end ray
end YM.UVExtension.Free
