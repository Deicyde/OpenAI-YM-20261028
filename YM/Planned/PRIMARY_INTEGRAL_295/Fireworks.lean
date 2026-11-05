import YM.Planned.PRIMARY_INTEGRAL_295.Harbors
import YM.Planned.PRIMARY_INTEGRAL_295.Nips
/-!
# Quantum earned at pre-registered Teller stage, along true Core.K

After-L before p/period etc. Recenter.K Forecast unforced section
data. Remaining assumptions alignment Root.Ringlets/H. Identity errors
from M cutoff with computed rate.Aim.Pre, include all seats and τ. No
proof polar F0 at masked.Sheet. For any Lxe service enter unscaled health
and post arithmetic afterwards. These proofs from Part I estimates.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Fireworks
open Function Filter Set Metric
open Labels Lattice RG Wilson Pressure Precision Exterior Tree Streets Carrier Bloch Place Next.Fluctuations
open Villa Fizz Fizz.Gush Bazaars Cedar  Oval
open Bunks Little Work.F01 Little.Core Push.Uniform Honey Drupes Density Mowing Festoons Work.F03 Xacts Sextants Nips
open Bid (pulled bills Sworn stretch)
open Progress.StationaryScenes
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius RealInnerProductSpace Classical
variable {G : Gauge} {c f : Side} {S:StepData c f}
variable (K:Core G S)(s:Signed)

lemma pulled_cost (x:Dir G c): ‖pulled x s‖≤‖x‖:=by
   apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).2; intro i; obtain ⟨i,rfl⟩:= (Work.E03.poleEquiv c).surjective i
   rw [twisted]; unfold bias; split <;> simp only [neg_smul,one_smul,norm_neg] <;> apply norm_le_pi_norm

lemma splash (Q:Teller G):∃ C:ℝ, 1≤C∧∀ c f(S:StepData c f) (K:Core G S), Teller.Funds Q S K.tube→∀ v:Dir G c, ∀ s:Signed,
    let a:=K.dawn v K.tube.R.A0
    ‖a‖ ≤ C*‖v‖ ∧ ‖pulled (K.outPeak v a) s‖ ≤ C*‖v‖:=by
   let D:=Streets.fee G*(Response.total Q.j Q.η Q.C+Real.exp Q.η)
   have he :0≤D:=by have hf:=Streets.fee_pos G; have hi:=Response.nonneg Q.j Q.η Q.C; unfold D Response.total Response.correction; positivity
   let C:=Honey.boxCard G; have hc:=Honey.boxCard_pos G
   refine ⟨C*D+1,by nlinarith,fun c f S K h v s=> ?_⟩
   intro a; let X:=K.tree; let W:= K.tube.R.A0; let A:=crick S X W (G:=G)
   have hb : ‖A‖ ≤ D:=by
      unfold D; rw [← h.atStep]; apply Streets.aim_cost _ _ _ _ Q.width.le
      have hp:= (h.crosses.2.2.2 [] (Nat.zero_le _)).1; simp only [Precision.advanceC,List.length_nil,add_zero,pow_one] at hp; exact hp
   have hx : ‖a‖≤D*‖v‖ := by
     let L:=Streets.streamFill S X (G:=G)
     have he':‖L (A v)‖≤D*‖v‖:= (L.le_opNorm _).trans ((mul_le_of_le_one_left (norm_nonneg _) (stream_cost S X)).trans ((A.le_opNorm _).trans (mul_le_mul_of_nonneg_right hb (norm_nonneg _))))
     refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i=> ((Moulin.absolute i.2 _).trans ((norm_le_pi_norm (L (A v)) i.1).trans he'))
   have hr : ‖rustic (S:=S) v‖≤‖v‖:=by
      apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr; intro i; obtain ⟨i,rfl⟩:= (Work.E03.poleEquiv f).surjective i
      unfold rustic; rw [Equiv.symm_apply_apply]; unfold linearCopy; split
      · rw [norm_zero]; positivity
      exact norm_le_pi_norm v _
   refine ⟨hx.trans (mul_le_mul_of_nonneg_right (by unfold C; nlinarith) (norm_nonneg v)), (pulled_cost ..).trans ?_⟩
   apply (norm_add_le ..).trans
   have ht := ((Bosom.placed K).le_opNorm a).trans (mul_le_mul (Honey.reach_fee K) hx (norm_nonneg _) (zero_le_one.trans hc))
   apply (add_le_add ht hr).trans_eq; ring

-- nearflat estimate combining actual buffers (always unturned V=1 at anchor).
section Ephemeral
variable {M C η θ : ℝ} {α β : Type*}[Fintype β] [Fintype α]
lemma incidence (P : α→β→ Pay G)(Q:α→β→Pay G) (h: NearFlat P Q M C) (_hm:0≤M) (_hC:0≤C)
    (f g:β→G.Color)(hf:∀i,‖f i-g i‖≤θ) (hg:∀i,‖g i‖≤η) (hp:0≤θ)(he:0≤η) (i:α) :
    ‖Pressure.zip P f i- Pressure.zip Q g i‖ ≤ M*θ+(M*C)*η:=by
   rw [show Pressure.zip P f i-Pressure.zip Q g i=Pressure.zip P (f-g) i + Pressure.zip (P-Q) g i from by unfold Pressure.zip; simp only [Pi.sub_apply,map_sub,sub_apply,Finset.sum_sub_distrib]; abel]
   exact (norm_add_le ..).trans (add_le_add (Work.E07.zip_uniform _ _ i (h.cut.rows i) hp hf) (Work.E07.zip_uniform _ _ i (h.close.rows i) he hg))
end Ephemeral

section Tolls
variable (p:Patch) (Q:Teller G)
lemma renaissance :∃ C τ : ℝ, 1≤C∧0<τ ∧ ∀ c f(S:StepData c f)(K:Core G S), S.patch=p→∀ H H', Rails.Ringlets Q K.tube H H' →
   ∀ i:Seats G c f, ∀ v:Dir G c,
      ‖(K.D 0).mulVec (K.dawn v K.tube.R.A0) i + fderiv ℝ (fun y=>K.F0 y i) 0 v‖ ≤ C*Real.exp (-τ*K.R)*‖v‖:=by
   obtain ⟨C,t,r,hC,ht,hr,h⟩:= Next.Fluctuations.kernel_chart_cost G p.L Q.η Q.C Q.width
   obtain ⟨U,hU,hu⟩:= Xacts.costs Q.top G; obtain ⟨V,hV,hv⟩:= Xacts.costs Q.below G
   obtain ⟨D,hD,hv'⟩:= splash Q
   let H:=U*D+2*C*V
   have hH:0≤H:=by unfold H; positivity
   let τ:=min t (min Q.top.width (Q.below.width/(p.L.val:ℝ)))
   have hw:0<τ:=lt_min ht (lt_min Q.top.width_pos (div_pos Q.below.width_pos (show (0:ℝ)<_ by exact_mod_cast p.L.property)))
   refine ⟨|ballast| *H+1,τ,by nlinarith [mul_nonneg (abs_nonneg ballast) hH],hw,?_⟩ --binder order fixed
   intro c f S K hp B A he i v
   let W:=K.tube.R.A0; let a:= K.dawn v W
   obtain ⟨⟨s,i⟩,j⟩:= i
   rw [Nips.precise K s a v he.high i j, norm_mul,Real.norm_eq_abs];
   let N:= K.R; let Q0:=Real.exp (-τ*K.R)
   have hQ:0≤Q0:= by unfold Q0; positivity
   have hc (v:ℝ) (h:τ≤v):Real.exp (-v*K.R)≤Q0:=by unfold Q0; gcongr
   obtain ⟨A₁,A₂,hy,hY⟩:=he.high.feeds
   let b:= pulled v s; let b':= pulled (K.outPeak v a) s
   have hB : ‖b'‖ ≤ D*‖v‖:= (hv' c f S K he.high v s).2
   have hb : ‖b‖≤‖v‖:= pulled_cost ..
   let X(j:Twin c):= xLin K.tube.low K.tube.down b j
   have hy'(j:Twin c): ‖X j‖ ≤ V*‖v‖ ∧ ‖xcopeLin K s v j-X j‖ ≤ V*Q0*‖v‖ := by
      obtain ⟨hf,hg⟩:=hv S.patch.L.val S.patch.L.property N c K.tube.down ⟨_,hY⟩ j b
      rw [← he.high.low] at hf hg; refine ⟨hf.trans (mul_le_mul_of_nonneg_left hb (by positivity)),?_⟩
      have he': Q.below.width / ↑S.patch.L.val≥τ:=by rw [hp]; apply (min_le_right ..).trans (min_le_right ..)
      rw [norm_sub_rev]; exact hg.trans (mul_le_mul (mul_le_mul_of_nonneg_left (hc _ he') (by positivity)) hb (norm_nonneg _) (by positivity))
   have hx'(j:Twin f) : ‖cutX K.tube.high K.tube.up b' 1 N j-xLin K.tube.high K.tube.up b' j‖≤ U*D*Q0*‖v‖:=by
      obtain ⟨hg,hf⟩:=hu 1 one_pos N f K.tube.up ⟨_,hy⟩ j b'; rw [←he.high.high,Nat.cast_one,div_one] at hf; rw [norm_sub_rev]
      have he : τ≤Q.top.width := (min_le_right ..).trans (min_le_left ..)
      apply hf.trans; apply (mul_le_mul (mul_le_mul_of_nonneg_left (hc _ he) (by positivity)) hB (norm_nonneg _) (by positivity)).trans_eq; ring
   have hZ := h S K.tube (by rw [hp]) ⟨_,he.high.crosses⟩ N 0 0 (by simp) hr.le
   rw [link_one] at hZ; simp only [widen,mul_zero,zero_add] at hZ
   have he₁ {α:Type} [Fintype α] (P : α→Twin c→Pay G) (Q :α→Twin c→Pay G) (ht:NearFlat P Q C (Real.exp (-t*N))) (x) :
      ‖Pressure.zip P (xcopeLin K s v) x-Pressure.zip Q X x‖ ≤ (2*C*V)*Q0*‖v‖ :=by
      have he:= incidence _ _ ht hC.le (Real.exp_pos _).le _ _ (fun j=>(hy' j).2) (fun j=>(hy' j).1) (by positivity) (by positivity) x
      apply he.trans; have hp: Real.exp (-t*K.R) ≤ Q0:= hc t (min_le_left ..)
      have ha := mul_le_mul_of_nonneg_left hp (show 0≤C*V*‖v‖ by positivity); change C * _+ C*Real.exp (-t*K.R)*_≤_; linarith
   let P:=(Sum.elim (tileF K s a v) (tileI K s a v) i)
   have hr : ‖P‖≤ H*Q0*‖v‖ :=by
      have hf:= K.full_zero v (s,i) he; rcases i with i|i
      · let A := Pressure.zip (flatF K.tube) X i
        have hl:xLin K.tube.high K.tube.up b' i=A:=sub_eq_zero.mp hf
        let L:=Pressure.zip (K.tube.Φ K.R 1) (xcopeLin K s v) i
        change ‖cutX K.tube.high K.tube.up b' _ _ i - L‖≤_
        have ht:= hx' i
        rw [hl] at ht; apply (norm_sub_le_norm_sub_add_norm_sub _ A L).trans; rw [norm_sub_rev A L]
        apply (add_le_add ht (he₁ (K.tube.Φ K.R 1) _ hZ.1 i)).trans_eq; unfold H; ring
      · let A := Pressure.zip (flatI K.tube) X i
        change ‖zLin S b' b i-Pressure.zip (K.tube.Φ' K.R 1) (xcopeLin K s v) i‖ ≤ _
        rw [show zLin S b' b i=A from sub_eq_zero.mp hf,norm_sub_rev]; apply (he₁ (K.tube.Φ' K.R 1) _ hZ.2.1 i).trans
        have hP:= show 2*C*V≤H by unfold H; nlinarith
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hP hQ) (norm_nonneg v)
   change _ ≤ (|ballast| *H+1)*Q0*‖v‖
   apply (mul_le_mul_of_nonneg_left ((Moulin.absolute j P).trans hr) (abs_nonneg _)).trans
   have hx:0≤Q0*‖v‖:=by positivity
   linarith

lemma inaugural (k:ℕ):∃ w:Trinket,0<w.radius ∧ ∀ c f(S:StepData c f)(K:Core G S), S.patch=p→∀ H H', Rails.Ringlets Q K.tube H H' → Bid.Larger (G:=G) S → Quantum K w K.tube.R.A0 k:=by
   obtain ⟨δ,C,hδ,hC,hY⟩:= Belays.showcase G (k+2) p Q
   obtain ⟨M,τ,hM,hτ,H⟩:= renaissance p Q
   let A:=Q.top.width; let x:=min τ (A/4)
   have he:0<A:=Q.top.width_pos; have hx:0<x:=lt_min hτ (by positivity)
   obtain ⟨B,hB,hF⟩:= Moulin.basket G (k+2) Q.top.clip Q.top.width he Q.top.paths Q.top.paths_pos.le
   obtain ⟨r,D,hr,hD,hI⟩:= Harbors.servants G (k+2) p Q.bind x hx
   obtain ⟨t,ht,hT⟩:= Bosom.hills G p.L p.J Q.bind Q.top.clip
   obtain ⟨Z,hZ,hA⟩:= splash Q
   let W:=C+M+B+D+Z
   let R:= min (min r δ) (1/2)
   have hW:1≤W:=by unfold W; linarith
   have hR:0<R:=lt_min (lt_min hr hδ) (by norm_num)
   let w:Trinket:= ⟨t,R,W,x,ht,hR.le,hW,hx⟩
   refine ⟨w,hR,fun c f S K hp A₁ A₂ hh hs=>?_⟩
   have hf:= hh.high; have hk:=hf.knobs; have hl:=congrArg Patch.L hp
   refine ⟨hT c f S K hs hk hl ?_ hf.high,fun i v hv=> (hY c f S K hp hf v ?_ i).mono ?_,fun i j v hv=>?_,bottom_t K hf,fun v=>?_,fun i v=>?_⟩ --hT ordering add Larger
   · exact congrArg Patch.J hp
   · exact hv.trans ((min_le_left ..).trans (min_le_right ..))
   · change C≤ W; unfold W; linarith
   · have hb : ∀ a b : Site c, Decay (A/4) a b ≤ Decay x a b := by
        intro a b; unfold Decay; gcongr; exact min_le_right ..
     obtain ⟨⟨s,i|i⟩,j'⟩:= i
     · obtain ⟨C',B',hz,hb'⟩:=hf.feeds
       apply (hF c f S K hf.high ⟨_,hz⟩ i j' s v (hv.trans (min_le_right ..)) j).mono
       exact mul_le_mul (by change B≤W; unfold W; linarith) (hb _ _) (decay_pos ..).le (zero_le_one.trans hW)
     have hn : p.Branches Q.bind G := by rw [← hp,← hk]; exact hs.1
     apply (hI c f S K hk hp hn s i j' j v (hv.trans ((min_le_left ..).trans (min_le_left ..)))).mono
     exact mul_le_mul_of_nonneg_right (by change D≤W; unfold W; linarith) (decay_pos ..).le
   · exact (hA c f S K hf v 1).1.trans (mul_le_mul_of_nonneg_right (by change Z≤W; unfold W; linarith) (norm_nonneg _))
   apply (H c f S K hp A₁ A₂ hh i v).trans
   change M*Real.exp (-τ*K.R) * _ ≤ W* Real.exp (-x*K.R) * _
   have he':M≤W:=by unfold W; linarith
   gcongr; exact min_le_left ..
end Tolls
end YM.Planned.PrimaryIntegral295.Fireworks
