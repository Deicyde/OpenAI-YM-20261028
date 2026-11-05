import YM.RG08.Flat.Curl
import YM.RG08.Packets.Limit

/-!
# kfalt for the flat Wilson quadratic precision. Full finer limit (arbitrary depth)

Fix all proof demands in advance. `Spacing` asks only length/plateau and delay inputs in addition
to the already accepted linear `retained_support` plan. Restricted to a single common RG schedule
on a stipulated tail `e` but across all finer cutoffs and all reporting ages there. `k` denotes
reporting scale, `i` the fixed-level output; may also be coarser than k. No period or phase choice
in this limit; the coefficients are those used for unmasked cover bulk before capture/quotient.

***Scope*** This file quantifies order zero in the vacuum prescription only. It compares the full
position-space quadratic log-germ coefficient (twice its coefficient if measuring ordered action
bilinear via K; see `Flat.output`, no 1/2, Hessian convention), NOT the off-curl two-form
extension, G, or any positive order or source kernels. Appears in *exactly* the stationary
prescription on each actual formal step, see `embedded` (doesn't require the path metric
extension coincide as long as its orientation contractions do). Later use kbulk for cumulant
iteration will also require the other flat kernels and graph/normalization estimates.
-/
noncomputable section
namespace YM.RG08.Flat
open Filter Finset Pert.Bulk Laurent Lattice Bloch Stationary Function Matrix RG08.Packets RG08.Rate RG Precision Next.Free Exterior
open scoped Topology ENNReal

set_option autoImplicit false
variable {G : Gauge} {a : Levels G} {H : Horizon a} {P : MapPrices}
  {S : Schedule} {Z : ℕ→ℝ} {w : ℕ→ℝ} {θ : ℝ} {e i : ℕ}

def clock (S : Schedule)(Z : ℕ→ℝ)(k i : ℕ):= 2+ Z k + |S.scale i-S.scale k|

structure Spacing (a : Levels G)(P : MapPrices)(Z w:ℕ→ℝ)(θ:ℝ)(e:ℕ) : Prop where
  Z_pos k : 0 ≤ Z k
  lit j : 0 < w j
  narrow j : w j ≤ P.α j
  small j : w j ≤ 1
  shared i : e ≤ i → w (a.clock.J i) ≤ bridgeWidth a P i
  gain : 0 < θ
  paid i : e ≤ i → quote a P i (w (a.clock.J (i+1))) ≤ ((a.S.block i).val:ℝ)^(-θ)
  crossing i : e ≤ i → 2*w (a.clock.J i) ≤ (a.S.block i).val * w (a.clock.J (i+1))
  age_cap : ∃ (A:ℝ)(d:ℕ),0≤A ∧ ∀ k j,e≤j → P.Ω (a.clock.J j) ≤ A * clock a.S Z k j^d

abbrev Road (e : ℕ) := ℕ×(Σ i:{t:ℕ//e≤t}, {n:ℕ//i.val≤n})

def berth (a : Levels G) (e:ℕ)(Z:ℕ→ℝ)(hZ:∀ k,0 ≤ Z k): World (Road e) G where
  trial _ := a
  low _ := e
  fine x := x.2.1.val
  extra x := x.2.2.val
  measure x := x.1
  Z x := Z x.1
  Z_nonneg _ := hZ _
  deep x := x.2.1.property
  earlier x := x.2.2.property

theorem Spacing.funded (hs : Spacing a P Z w θ e)(h:H.Suffices P) : (berth a e Z hs.Z_pos).Funding P w θ := by
  refine ⟨hs.lit,hs.narrow,fun x i hi _=> hs.shared _ hi.1,hs.gain,fun x i hi _=> hs.crossing _ hi.1,fun x i hi _=> ?_,?_⟩
  · rw [Rate.Stair.drop_length]; exact hs.paid _ hi.1
  obtain ⟨A,d,hA,hB⟩:= hs.age_cap
  refine ⟨Fintype.card Faces*(A+A),d,by positivity,fun x i hi=>?_⟩
  dsimp only; split
  · have ht:= Ω_pos h i
    change 0 ≤ topTab a P i ∧ topTab a P i ≤ (Fintype.card Faces : ℝ) * (A+A)*clock a.S Z x.1 i^d
    unfold topTab
    have hr := hB x.1 i hi.1
    exact ⟨by positivity,(mul_le_mul_of_nonneg_left (add_le_add hr hr) (by positivity)).trans_eq (by ring)⟩
  have ht := Rate.Stair.age_big (berth a e Z hs.Z_pos).bar x i
  exact ⟨le_rfl,mul_nonneg (by positivity) (pow_nonneg ((le_trans (by norm_num) ht)) _)⟩

lemma mesh_sides (S : Schedule) (m:ℕ) : Tendsto (fun n=>(S.side m n).val) atTop atTop := by
  refine tendsto_atTop_mono (f:=fun i=>(S.period i).val) (fun i=>?_ ) S.period_strict.tendsto_atTop
  exact Nat.le_mul_of_pos_right _ (S.denominator m).pos

/-- Quantitative row UV convergence, under adjacent-stage schedule data. -/
theorem meshed (hs : Spacing a P Z w θ e) (h : H.Suffices P)
   (hp : ∀ (i N:ℕ), e ≤ i → i<N → (H.towers N i).T=((destination a N i).duo a.clock.kernel.penalty).T) :
    let y i := w (a.clock.J i)
    ∃ (A:ℝ) (d:ℕ) (c:ℝ), 0≤A ∧ 0<c ∧
      ∀ (k i N n:ℕ), e ≤ i → i≤N → N≤n → RowCost (y i) 1 (fun x z=> output (H.H n i) x z-output (H.H N i) x z)
        (A*clock a.S Z k i^d * ((a.S.a N/a.S.a i)^c)) := by
  intro y
  let W := berth a e Z hs.Z_pos
  let M (x:Road e):Horizon (W.trial x):=H
  have hρ : World.Provides M P := ⟨fun _=>h,fun _ i=>hp i _⟩
  obtain ⟨K,A,d,c,hA,hC,Hr⟩:= World.overlap hρ (hs.funded h)
  refine ⟨sumToken*A,d,c,mul_nonneg sumToken_pos hA,hC,fun k i N n hi hIN hN =>?_⟩
  let x : Road e := (k, ⟨⟨N,hi.trans hIN⟩,n,hN⟩)
  have hr := Hr x i (show W.bar.Here x i from ⟨hi,hIN⟩)
  change FlatRep H N n i (y i) (A * clock a.S Z k i^d * ((a.S.a N/a.S.a i)^c)) (K x i) at hr
  let B := H.H n i; let D:=H.H N i
  have hq := Ω_pos h i
  have ht := hs.narrow (a.clock.J i)
  have hv : 0 < y i:= hs.lit _
  have hw : y i ≤ 1:= hs.small _
  let s := P.Ω (a.clock.J i)
  have he : B.metric.strip (y i) s := fun u z=> ((h.rows n i (hIN.trans hN)).2.1 u z).mono ht le_rfl
  have hh : D.metric.strip (y i) s := fun u z=> ((h.rows N i hIN).2.1 u z).mono ht le_rfl
  have hΛ : 2≤ clock a.S Z k i := Rate.Stair.age_big W.bar x i
  have hK:0≤ A * clock a.S Z k i^d * ((a.S.a N/a.S.a i)^c) := by
    have ht := a.S.a_pos N; have hg := a.S.a_pos i; have hr:0≤clock a.S Z k i:= le_trans (by norm_num) hΛ; positivity
  convert (resolve (K:=K x i) (mesh_sides a.S i) hr.here he hh hq hv.le hw hr.declared hv.le hw hK).2 using 1; ring

private def meshE (σ : ℝ) : Expense (J:=Market Links × Links) (fun _=>Cover):= fun z x=> σ*delta (1:Side) z.1.1 x

/-- In the same width (no output-to-topology count-dependent loss). Gives every fixed
position-moment under finite further width discount; address/field-free. -/
theorem supplies (hs : Spacing a P Z w θ e) (h : H.Suffices P)
   (hp : ∀ (i N:ℕ), e ≤ i → i<N → (H.towers N i).T=((destination a N i).duo a.clock.kernel.penalty).T) :
    let y i := w (a.clock.J i)
    ∃ (F:ℕ→Kernel Links Links)(A B:ℝ)(d l:ℕ)(c:ℝ), 0≤A ∧ 0≤B ∧ 0<c ∧ ∀ k i, e ≤ i →
       RowCost (y i) 1 (F i) (B * clock a.S Z k i^l) ∧
       (∀ m z,Tendsto (fun n=> output (H.H n i) m z) atTop (𝓝 (F i m z))) ∧
       ∀ N,i≤N → RowCost (y i) 1 (fun x z=> output (H.H N i) x z-F i x z) (A * clock a.S Z k i^d * ((a.S.a N/a.S.a i)^c)) := by
  intro y
  obtain ⟨A,d,c,hA,hc,Hc⟩:=meshed hs h hp
  obtain ⟨B,l,hB,Hb⟩:=hs.age_cap
  let u (k i N) := A * clock a.S Z k i^d * ((a.S.a N/a.S.a i)^c)
  let v (k i) := sumToken*Fintype.card Faces*(B*clock a.S Z k i^l)
  let R i n := output (H.H n i)
  have ht i k (hi:e ≤ i) : ∃ F, RowCost (y i) 1 F (v k i) ∧
       (∀ m z,Tendsto (fun n=> R i n m z) atTop (𝓝 (F m z))) ∧
       ∀ N,i≤N → RowCost (y i) 1 (fun x z=> R i N x z-F x z) (u k i N) := by
    let D (n:ℕ) (z:Market Links × Links) (x:Cover) := R i n z.1 (x,z.2)
    have hU : Tendsto (u k i) atTop (𝓝 0) := by
      have ht := a.S.shrinks.div_const (a.S.a i)
      have hu := ht.rpow (tendsto_const_nhds (x:=c)) (Or.inr hc)
      simpa only [u,_root_.zero_div,Real.zero_rpow hc.ne',mul_zero] using hu.const_mul (A*clock a.S Z k i^d)
    have hq : 0 ≤ y i:= (hs.lit _).le
    have hX : ∀ n m, i ≤ n → n ≤ m → Ticket (meshE (y i)) (fun z x=>D n z x - D m z x) (u k i n) := fun n m hn hm z=> by
      have h := Hc k i n m hi hn hm z.1 z.2
      convert h using 1
      apply tsum_congr; intro x
      rw [stamp_real, bill,bill,abs_sub_comm]
      rfl
    have hu (N:ℕ) : 0 ≤ u k i N := by
      have hz := a.S.a_pos N; have hm:=a.S.a_pos i
      have hk:=hs.Z_pos k; unfold u clock; positivity
    have hr n (hn:i ≤ n): Ticket (meshE (y i)) (D n) (v k i):= fun z=> by
      change (∑' x,stamp (R i n z.1 (x,z.2)) _) ≤ _
      simp_rw [stamp_real]
      obtain ⟨HA,-⟩:=output_cost (Y:=H.H n i) (p:=P.Ω (a.clock.J i)) (σ:=y i)
        (fun x z=> ((h.rows n i hn).2.1 x z).mono (hs.narrow _) le_rfl) (Ω_pos h i) hq (hs.small _)
      apply (HA z.1 z.2).trans
      apply ENNReal.ofReal_le_ofReal
      unfold v
      rw [mul_assoc]
      have ht := sumToken_pos
      gcongr; exact Hb k i hi
    obtain ⟨V,hT,H',HH⟩:= solvent (K:=D) i (fun j x=>mul_nonneg hq (delta_nonneg ..)) hU hX (fun N _=> hu N) _ ((eventually_ge_atTop i).mono hr)
    refine ⟨fun m z=> V (m,z.2) z.1,?_,fun m z=>hT (m,z.2) z.1,?_⟩
    · intro m z
      simpa only [meshE,earning,stamp_real] using HH (m,z)
    intro N hn m z
    simpa only [meshE,earning,D,stamp_real] using H' N hn (m,z)
  classical
  choose Y hg hz hv using fun (i : { i // e ≤ i}) k=> ht i.val k i.property
  have Hj (i : { i // e ≤ i}) k : Y i 0 = Y i k := funext fun m=>funext fun z=> tendsto_nhds_unique (hz i 0 m z) (hz i k m z)
  refine ⟨fun i=> if he:e ≤ i then Y ⟨i,he⟩ 0 else 0,A,sumToken*Fintype.card Faces*B,d,l,c,hA, mul_nonneg (mul_nonneg sumToken_pos (Nat.cast_nonneg _)) hB,hc,?_⟩
  intro k i he
  dsimp only
  rw [dif_pos he,Hj _ k]
  have hh : sumToken*Fintype.card Faces*B*clock a.S Z k i^l = v k i := by unfold v; ring
  rw [hh]
  exact ⟨hg ⟨i,he⟩ k,hz ⟨i,he⟩ k,hv ⟨i,he⟩ k⟩
end YM.RG08.Flat
