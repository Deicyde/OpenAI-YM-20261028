import YM.OPE.Sweep.Induct

/-!
# Winter: terminal join

Adapt the normalization step and proof common to `Ribbons.{Harvest,Arco,Dolphin}`;
uses the same `Throws` purchase for the actual coefficients after merging. Conservation
of the reaped product lets us disregard the intermediate choices of fiber labels.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.ManyCopies
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Source Accent Ribbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Multi GridApprox.Nil
open Extra.Trajectories MergeProof.Float Next.Rank Station Corona
open scoped Topology BigOperators Classical
variable {Z V I J T : Type}[Fintype V][DecidableEq V][Fintype I][DecidableEq I]
  [Fintype J][DecidableEq J]{G:Gauge}{n:Side}
variable {A:History G}{N p k m i j d:ℕ}
    {δ φ σ χ:ℕ→ℝ}{r:ℕ→ℕ}{D:∀ N p m:ℕ,m<N→GaugeDoor (A.rep N p (m+1)) (A.rep N p m)}
    {E:∀ i:ℕ, V→Site (A.S.side i p)}{P:V→Motion}{v:V}{B:V→Equiv.Perm V}{o:∀ i:ℕ,V×I→Site (A.S.side i p)}
set_option quotPrecheck false
local notation "Γ" => A.levels.clock.op m p
local notation "R" => A.rep N p
local notation "Y'" => A.levels.budget
variable {Q:∀ i:ℕ,i≤N→ Config G (A.S.side i p)→Poly (Names V I)} {W W':I→ℝ}{c: V×I→ℂ}{H l : ℕ}
    (h:A.Selected)(ht:Thor A δ r D σ χ k)

lemma ripe {y: V×I→ Config G (A.S.side N p)→ℂ} (i₀:I)(hm:i≤N) (hp:Integrable (birth (Names V I) (R N) y) (prior G _)) : gust A N p N (birth (Bud V) (R N) (fun j u=>∏ x,y (j,x) u)) i hm=
    fun U=> Fibers.reap (finishGroup V i₀) (gust A N p N (birth (Names V I) (R N) y) i hm U):=by
    induction hm using Nat.decreasingInduction with
    | self=>
      funext U; rw [gust_base,gust_base]; ext s; change ((birth _ _ _) U).part s=((birth _ _ _) U).part ((finishGroup V i₀).plena s); unfold birth Mach; simp only [Poly.part_smul, pass_fire]; congr 1; rw [Fibers.prod_plena]; refine prod_congr rfl fun j _=>?_; rw [contentF,prod_image]; exact fun _ _ _ _ h=>Prod.mk.inj h|>.2
    | of_succ i hi IH=>
      rw [gust_step _ _ _ _ _ hi, IH]; funext U; rw [gust_step _ _ _ _ _ hi]; unfold StepData.push; let L:= (Fibers.reap (finishGroup V i₀)).restrictScalars ℝ; have he:=L.integral_comp_comm (StepData.push_slice (A.levels.transition_mass i p (A.β N p (i+1))) U _ (gust_live A N _ _ _ hp hi)); simp_rw [L.map_smul] at he; exact he
variable {z x:ℝ} (i₀:I) (hm:m<N)
local notation "T'"=> (Labels.frames G).level d
local notation "U" => Next.Foundations.localSection G d
local notation "M'" => (A.S.a (m+1)^d*(x*(4*(1/z))))
local notation "X1"=> A.rep N p (m+1)
local notation "P0"=> A.levels.budget m
local notation "P1"=> A.levels.budget (m+1)
local notation "L"=> (↑(A.S.block m).val:ℂ)^d
local notation "ω"=> (fun i : V=> (Γ).ratio.embed (E m i))
local notation "Q*"=> (fun U_=>Fibers.reap (finishGroup V i₀) (Q (m+1) hm U_))

variable {W₀:V→ℝ}
include h ht hm
lemma Live.winter
    (hc:Live A N p E o P v B Q δ χ (m+1) hm W c)
    (hk:k ≤ m) (he: E m v=0)(ho:E (m+1)=ω)(h₀:∀ i,o (m+1) (i,i₀)=E (m+1) i)(hW:P v=(1,false))
    (hI:Occupancy (E m) (r m))(hO:Occupancy (E (m+1)) (r m)) (hp:Occupancy (o (m+1)) (r (m+1)))(hP:Collar (o (m+1)) v (E (m+1)) P)
    (hH:0<H)(hF:Fintype.card I ≤ H)(hB:ClusterPars A δ χ r (m+1))
    (hQ:Integrable (Q (m+1) hm) (prior G _))
    (hS:∀ j:V×I, coverNumber (Y' (m+1)).B ({o (m+1) (j.1,i₀),o (m+1) j}:Support _ ) ≤ l)
    (hD: Throws A N p m (D N p m hm) (Next.Foundations.hol G) (U) x)(hx:1≤x)
    (ha:∀ i,0 < W₀ i)(hε:∀ i,W₀ i ≤ δ m*(z/(16*x))) (hz: 0 < z)(hy:z ≤ cashIn A δ H l (m+1) W) :
    ∃ Q₀: Coefficient T' (A.S.side m p), Q₀.Format 0 (Next.Foundations.hol G) (R m) ∧ Q₀.remBound 0 (R m) (kappa A m) M' ∧ (T').coeffSize Q₀.x ≤ M' ∧
       Served (R m) (fun i=> radiant (alto A m d) (P i) (E m i) (Q₀.exponentialEntry 0 U (R m))) (fun i=> sunny (R m) Q₀.forced (P i) (E m i) (alto A m d)) ((Γ).push (X1).beta Q*) (E m) W₀ ((P0).supportExponent) 1:=by
    have hV:=(ht.moon N p m hk hm).1; have hL:=ht.suns m hk
    obtain ⟨g,L₀,hY,hK,hZ⟩:= Live.terminal H l h hm hc hB hV.contact hH hF hp hP i₀ hS
    have he': (fun i:V=>o (m+1) (i,i₀))=ω:=(funext h₀).trans ho; rw [he'] at hY
    let t:= cashIn A δ H l (m+1) W; let I'(i:V):=z/(16*x); have hy':0<t:= hz.trans_le hy; have hu:0<x:=zero_lt_one.trans_le hx; have hw(i):0<I' i:= div_pos hz (by positivity)
    have hb(i):I' i≤ t:= le_trans (div_le_self hz.le (show 1 ≤ 16*x by linarith only [hx])) hy
    let f':=fun i=>profile (X1).activities (L₀ i); have hC := hY.prune (fun _=>hy') hw (slighter (fun _=>hy') hw (w:=1) (fun i=>(hb i).trans_eq (one_mul _|>.symm)) zero_le_one le_rfl) zero_le_one (show (P1).supportExponent+0 ≤ (P1).supportExponent from by simp) (show 1*1≤(1:ℝ) from by norm_num)
    have hβ: ω v=0:=by dsimp only; rw [he]; exact (Γ).ratio.root.map_zero
    have ha': Blade X1 0 (g v) (f' v) 0 (4*(1/z)):=by
       have h₁:= (hK v).2; rw [congr_fun he' v|>.trans hβ] at h₁ -- perhaps doesn't find actual
       apply h₁.more; gcongr
    have he'(i):g i=stepUp (P i) (ω i) (g v)∧f' i=floatUp (P i) (ω i) (f' v):=by
       by_cases hi:i=v; · subst i; rw [hW,hβ,stepid,floatid];exact ⟨rfl,rfl⟩
       have hf:=hZ i hi; rw [ho] at hf; exact hf
    have hξ : Repegs (E m) (Y' m).B (fun i=>δ m*I' i) W₀ (1/2) 1 (Bud V):=by
       intro i he j hj; rw [one_mul]; exact (prod_le_prod (fun i _=>ha i|>.le) (fun i _=>hε i)).trans (le_mul_of_one_le_right (prod_nonneg (fun i _=>mul_nonneg hL.hats.1.le (hw i|>.le))) (Real.one_le_exp (by positivity)))
    have hA'(i): 2*I' i*(2*(4*(1/z)))≤1:=by unfold I'; field_simp; linarith only [mul_le_mul_of_nonneg_left hx hz.le,hx,hz]
    have hX(i): I' i*(‖(L)⁻¹‖*(x*(4*(1/z))))≤1:=by
       have hh:1≤ ‖L‖:= by rw [norm_pow,Complex.norm_natCast]; exact one_le_pow₀ (le_trans one_le_two (size_enough A m))
       have hn:‖(L)⁻¹‖ ≤ 1:= by rw [norm_inv]; exact inv_le_one_of_one_le₀ hh
       refine (mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (mul_nonneg hu.le (by positivity)) hn) (hw i).le).trans ?_; unfold I'; field_simp; linarith
    obtain ⟨Q₀,hY,hσ,hA,hX⟩:= fuseNext A d r h hm (ht.suns m hk) hV hw ha hC (by linarith only) (ho ▸ hO) (by rw [show (Γ).ratio.parent ∘ ω=E m from funext (fun i=>(Γ).ratio.embed_parent _)]; exact hI) (fun i=>(hK i).1) ha' rfl he' hD hu.le hA' hX hξ (((Fibers.reap (finishGroup V i₀)).restrictScalars ℝ).integrable_comp hQ)
    exact crescent A d hY hσ hA hX
end YM.MergeProof.Ribbons.ManyCopies
