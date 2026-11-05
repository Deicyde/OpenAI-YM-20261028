import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Tablets
import YM.Extra.MULTISOURCE_TRAJECTORIES.Rents
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Stagecraft
import YM.PhysicalNext.PHYSICAL_JOINT_ENDPOINT_LOAD_F16.DLog.Fund
import YM.Progress.JOINT_CALENDAR.Period
import YM.Push.ABSOLUTE_SUMS.Path
import YM.Push.RELAY_DIFFERENCE.Dictionary

/-!
# Price the value-level open chains from the two Cs (same sector)

Adapt the `RelativeLogdet` Hit price here to SEC quadratic term. No
endpoint condition (dust at both ends); color tapes are not yet used or
summed. Still need to pay z or broader projection for each endpoint.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Barge
open Lattice Wilson Pressure RG RG.Supply Matrix Finset Filter Tree
    Next.SectorChange Next.SectorChange.Rows Push.SectorMeasure Pressure.Stores
    Function AnalyticBridge.RelativeLogdet Physical Push.AbsoluteSums FreeResolvent
    AnalyticBridge.LocalGaussianLaws Dictionary Dictionary.Wires Dictionary.Notify
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f} {A : Stores S} {F : Forest S.ratio}
    {V : Config G c} {P : Teller G} {D : Patch} {T : Tube G S} {i : Site c} {x a v C η b : ℝ}

section coast
variable {ι : Type} [Fintype ι] [DecidableEq ι] {p : ι→ Site c} {L θ V q : ℝ} {l B : ℕ}
abbrev Trip (ι : Type) := (m:ℕ) × (ι × ι × (Fin (m+1) →ι))
def berth (p : ι → Site c) (l B : ℕ) (w : Trip ι) : Support c:= pocket p l B w.2.1 w.2.2.1 w.2.2.2
def stamp (p : ι → Site c) (B : ℕ) (v C q : ℝ) (w : Trip ι) : ℝ :=
    let Y:=fares (native c) p v
    if jumps (AnalyticBridge.RelativeLogdet.nearby p B) w.2.1 w.2.2.1 w.2.2.2 then C*q^(w.1+1)*road Y Y w.2.1 w.2.2.1 w.2.2.2 else 0

omit [DecidableEq ι] [Fintype ι] in
lemma stamp_nn (p : ι → Site c) (B : ℕ) (v : ℝ) (hC : 0≤C) (hq : 0≤q) (w : Trip ι) : 0 ≤ stamp p B v C q w:= by
  unfold stamp; split
  · exact mul_nonneg (by positivity) (road_pos _ _ (fun _ _=> fares_nn ..) (fun _ _=>fares_nn ..) ..)
  exact le_rfl

omit [DecidableEq ι] in
lemma run_fee (hL :0≤L) (hK : (native c).Volume p v L) (n : ℕ) (i : ι) :
    let Y:= fares (native c) p v
    (∑ j : ι,∑ w : Fin n→ι, road Y Y i j w)≤ L^(n+1):= by
  intro Y; induction n generalizing i with
  | zero=> simp only [road,zero_add,pow_one,sum_const,card_univ,Fintype.card_fun,Fintype.card_fin,pow_zero,one_smul]; exact hK.bound (p i)
  | succ m ih=>
    simp_rw [AnalyticBridge.RelativeLogdet.sum_cons, road_succ, ← Finset.mul_sum]; rw [Finset.sum_comm (s:=Finset.univ)]
    simp_rw [← Finset.mul_sum]; refine (Finset.sum_le_sum (fun a _=> mul_le_mul_of_nonneg_left (ih a) (fares_nn ..))).trans ?_
    rw [← Finset.sum_mul,pow_succ' L (m+1)]; exact mul_le_mul_of_nonneg_right (hK.bound (p i)) (pow_nonneg hL _)

omit [DecidableEq ι] in
private lemma open_length (hC : 0≤C) (hq : 0≤q) (hB : 0<B) (hl : 1≤l)
    (ha : 0≤a) (ht : 0≤θ) (hL : 0≤L) (hK : (native c).Volume p v L) (h : (native c).Volume p θ V) (m : ℕ) (s : Site c) :
    let f w:= if s∈berth p l B w then stamp p B v C q w * Real.exp (a*coverNumber B (berth p l B w)) else 0
    (∑ w:ι×ι×(Fin (m+1)→ι), f ⟨m,w⟩) ≤ permitCost 2 L V C q a θ l B * AnalyticBridge.RelativeLogdet.pass L q a θ l B^m := by
  intro f; let Y:=fares (native c) p v; let G:= Real.exp (a*tilePrice l); let E:= Real.exp (θ*(B:ℝ)); let J:= fun i=>(native c).weight (-θ) s (p i)
  let P:= E^(m+3+l); let H:=G^(m+4); let N:=C*q^(m+1)
  have he:0≤P:=by unfold P E; positivity
  have hh:0≤H:=by unfold H G; positivity
  have hn:0≤N:=by unfold N; positivity
  have hp (i : ι):0≤J i:=(native c).weight_nn ..
  have h1 (i j : ι) (x : Fin (m+1)→ι) : f ⟨m,i,j,x⟩ ≤ P*H*N*(J i*road Y Y i j x):= by
    have hr:0≤road Y Y i j x:= road_pos _ _ (fun _ _=>fares_nn ..) (fun _ _=>fares_nn ..) ..
    have h2:0≤P*H*N*(J i*road Y Y i j x):= mul_nonneg (by positivity) (mul_nonneg (hp i) hr)
    unfold f; split
    next hu=>
      unfold stamp; split
      next hs=>
        let w:= pocket p l B i j x
        have hy : Real.exp (a*coverNumber B w)≤ H:= by
          have hx : (coverNumber B w:ℝ) ≤ (m+4:ℕ)* (tilePrice l:ℝ):= by
            exact_mod_cast (pocket_cost p hB hl i j x hs).trans (Nat.mul_le_mul_right _ (by omega : m+1+2 ≤ m+4))
          unfold H G; rw [← Real.exp_nat_mul]; exact Real.exp_monotone ((mul_le_mul_of_nonneg_left hx ha).trans_eq (by ring))
        have hP :1≤ J i * P:= by
          unfold J P E Cost.weight; rw [← Real.exp_nat_mul,← Real.exp_add]; apply Real.one_le_exp
          change 0≤ -θ * separation s (p i) + _*(θ*(B:ℝ))
          rw [separation_comm]; have hz : (separation (p i) s:ℝ) ≤ (m+3+l:ℕ)*(B:ℝ):= by
            exact_mod_cast (pocket_span p x hs (show s∈w from hu)).trans (Nat.mul_le_mul_right _ (show m+1+1+l ≤ m+3+l by omega))
          nlinarith only [mul_le_mul_of_nonneg_left hz ht]
        exact (mul_le_mul_of_nonneg_left hy (mul_nonneg hn hr)).trans ((le_mul_of_one_le_left (mul_nonneg (mul_nonneg hn hr) hh) hP).trans_eq (by ring))
      dsimp only; rw [zero_mul]; exact h2
    exact h2
  let D:= P*H*N; have hD:0≤D:=by unfold D;positivity
  simp_rw [Fintype.sum_prod_type]; apply le_trans (Finset.sum_le_sum (fun i _=> Finset.sum_le_sum (fun j _=> Finset.sum_le_sum (fun x _=>h1 i j x))))
  simp_rw [← Finset.mul_sum]
  exact (mul_le_mul_of_nonneg_left ((Finset.sum_le_sum (fun i _=>mul_le_mul_of_nonneg_left (run_fee hL hK (m+1) i) (hp i))).trans ((Finset.sum_mul ..).symm.trans_le (mul_le_mul_of_nonneg_right (h.bound s) (pow_nonneg hL _)))) hD).trans_eq (by
    change D*(V*L^(m+1+1))=_; unfold D H P N permitCost AnalyticBridge.RelativeLogdet.pass G E; rw [show m+3+l=m+(2+1+l) by omega]; simp only [pow_add,pow_one,mul_pow]; ring)

omit [DecidableEq ι] in
lemma open_pass (hC : 0≤C) (hq : 0≤q) (hB : 0<B) (hl : 1≤l) (ha : 0≤a) (ht : 0≤θ) (hL : 0≤L)
    (hK : (native c).Volume p v L) (h : (native c).Volume p θ V) (hc : AnalyticBridge.RelativeLogdet.pass L q a θ l B<1) :
    Ac.Hit (berth p l B) B (stamp p B v C q) a (totalCost 2 L V C q a θ l B) := by
  intro s
  let f w:= if s∈berth p l B w then stamp p B v C q w * Real.exp (a*coverNumber B (berth p l B w)) else 0
  have hg:0≤AnalyticBridge.RelativeLogdet.pass L q a θ l B:=by unfold AnalyticBridge.RelativeLogdet.pass; positivity
  have he: ∀ w,0≤ f w:=by intro w; unfold f; split; exact mul_nonneg (stamp_nn p B v hC hq w) (Real.exp_pos _).le; exact le_rfl
  let H:= permitCost 2 L V C q a θ l B; have ht' := (hasSum_geometric_of_lt_one hg hc).mul_left H
  have hp (m : ℕ): (∑' w,f ⟨m,w⟩)≤ H*AnalyticBridge.RelativeLogdet.pass L q a θ l B^m:= by rw [tsum_fintype]; exact open_length hC hq hB hl ha ht hL hK h m s
  have hv := ht'.summable.of_nonneg_of_le (fun m:ℕ=>tsum_nonneg (fun w=> he ⟨m,w⟩)) hp
  have hh := (summable_sigma_of_nonneg he).mpr ⟨fun _=>.of_finite,hv⟩
  exact ⟨he,hh,(hh.tsum_sigma' (fun _=>.of_finite)).trans_le ((hv.tsum_le_tsum hp ht'.summable).trans_eq ht'.tsum_eq)⟩
end coast

lemma embark (ha :0≤a) (hb :0<b) (hv : 0<v) (hC : 0≤C) (G : Gauge) (D : Patch) (l : ℕ) (hl : 1≤l) :
    ∀ᶠ B in atTop, ∀ {c f : Side} (S : StepData c f), S.patch=D →
      Ac.Hit (berth (place S (G:=G)) l B) B (stamp (place S) B v C (currency b B)) a (currency (b/3) B):= by
  let θ:= b/(3*(l+3:ℕ)); let L:= Physical.ceiling G D v; let V:=Physical.ceiling G D θ
  have ht :0<θ:= by unfold θ; positivity
  have he:θ*(l+3:ℕ)=b/3:= by unfold θ; field_simp
  have hy:2+1+l=l+3:=by omega
  have hz:θ<b:=by nlinarith only [he,hb,mul_le_mul_of_nonneg_left (show (1:ℝ) ≤ (l+3:ℕ) by exact_mod_cast (show 1≤l+3 by omega)) ht.le]
  have hL:0≤L:=ceiling_nn ..
  filter_upwards [eventually_gt_atTop (0:ℕ),worth a l 2 (show 0≤V from ceiling_nn ..) hL hC hz (show b/3< b-θ*(2+1+l:ℕ) by rw [hy, he]; linarith only [hb])] with B hB hh c f S hS
  exact fun s=> budget_loosen (open_pass hC (currency_pos ..).le hB hl ha ht.le hL
    (by unfold L; rw [← hS]; exact audience S G hv : (native c).Volume (Physical.place S (G:=G)) v L) (by unfold V; rw [← hS]; exact audience S G ht) hh.1 s) hh.2

-- Use the actual Borel stencil spelling. (palette=fog at endpoint.)
variable (k : S.Choices) (ht : Boosted T P x) (h : Positioned x A V) (hc : Physical.Certified S T x v C η b)
include ht hc h
lemma award : let Y:=Wires.beam T k V x A F; let Q:=Wires.cloudX T x k V A F; let B:=radiusB x; let q:=currency b B
    (∀ i j : Full G f, HasSum (forward Y Q i j) ((Q⁻¹-Y) i j)) ∧
      ∀ w: Trip (Full G f), |forward Y Q w.2.1 w.2.2.1 ⟨w.1,w.2.2.2⟩| ≤ stamp (place S (G:=G)) B v C q w:= by
  intro Y Q B q
  obtain ⟨s,hs⟩:= ht.license A F V h; let W:= Physical.windows S x (G:=G)
  have hy : Y=Physical.AFull T A F x V k:=Wires.beam_exact T k V x A F ht.produced hs
  have hP : Priced (native c) (place S) W Y v C q:= hy.symm ▸ hc.writes F k h
  have he:Schur.clouded W Y=Q:=rfl
  have hv : Q.PosDef:=by unfold Q cloudX; change (Schur.clouded W Y).PosDef; rw [hy]; exact (hc.fogs F k h).2
  let p:=place S (G:=G); have hh:=Aperture.spare (beam_aperture T ht.produced k V A F)
  have hr : 1-Q*Y = (-(excess W Y)).transpose := by
    unfold excess; rw [he, transpose_neg,transpose_sub, Matrix.transpose_one,transpose_mul,(isHermitian_iff_isSymm.mp hP.gram.isHermitian).eq,(isHermitian_iff_isSymm.mp hv.isHermitian).eq]; abel
  have hb : (native c).Schur p p v q (Y*Q-1):= he ▸ hP.mix
  have hC:=zero_le_one.trans hP.paid
  refine ⟨fun i j=> (chain_receipt hP.kernel hb hP.rate hC hP.coupon hc.small hP.gram hv i j).2,fun w=>?_⟩
  unfold stamp forward; dsimp only; rw [hr]; split
  · exact road_fares hP.kernel hP.mix.neg.transpose hC hP.coupon w.2.1 w.2.2.1 w.2.2.2
  next hl => rw [road_drop _ _ ?_ hh.neg.symm _ _ _ hl,abs_zero]; exact (beam_aperture T ht.produced k V A F).1.trans (Nat.div_le_self ..)
end YM.PhysicalNext.InteractingRank.Barge
