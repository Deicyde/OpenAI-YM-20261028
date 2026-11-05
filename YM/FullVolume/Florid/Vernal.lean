import YM.FullVolume.Florid.Land
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Empire.Imago
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid
open ConnectedActivityE6 Shell Channel Oriented SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Matter
open Blaze Silica Scroll Vine Stained Polar Shield Flux Eider Reserves Brush Metric Foramen Gate Tablet
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open PhysicalNext.Repeat PhysicalNext.Repeat.Alabaster FullVolume.Ray Daisy Lotus
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {P : Teller G} {W : ℝ}
variable {Q : ConnectedActivityE6.Target G P} {o : ConnectedActivityE6.Target.Order G W} {R : RG.Rep G f}
    {x₀ μ C:ℝ} {H : Cash W x₀ μ L Q o C T R}
    {v s t b δ A n B : ℝ} {j k : ℕ}
variable {F : Tree.Forest S.ratio} {i η r q u d L' A' fq:ℝ} {K:ℕ} {χ:Chi}
open Lyre Jams
set_option quotPrecheck false
variable {U:Tune H v δ} (M:Lyre U j u d r A' χ A b L' K)
namespace Mill
variable (V:Mill U)
local notation "Λ"=> U.pole
local notation "Rv"=> V.pole
variable (D: dust j o χ L x₀ d fq)
variable (X : Coat T F)
variable {E:Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {U₀:E→ Config G c} {s:E} (hx:X.x=x₀)(he:X.width=o.K)(hv:X.χ=χ)(hm:X.manifest)(hy:U₀ s=X.V)(hU:Mode U₀ s j u)
variable (z:Air f G)
local notation "τ" => (Rv).turn.badge S
local notation "β"=> R.beta
local notation "w₀"=> radiusB x₀
local notation "I₀" => X.input (worldZ X β z)
local notation "f₀" => fun i=> steer X A (worldZ X β z) (U₀ i)
local notation "z₀" => fun i=> course X A β z (U₀ i)
local notation "Yd"=> fun i=> vary X (U₀ i)

variable {p:Signal j} {ν α:ℝ} (hc:Clear Q L μ ν x₀ v p) (hr:Clarity H j A' δ ν)
local notation "m'"=> (F.order G).prod X.dice
local notation "m₀"=> M.meadow ν p
set_option quotPrecheck false
open Lyre
variable {V':ℝ→ℝ} (W':Lake G L (payE o.eta o.gap o.ample (Census.tubularPrice G L)) (K*j*2) V' k)
variable (Y':Margin G L x₀ α δ) (w:Rung) (η:ℝ) (hh : ∀ i:ℕ, ‖FullVolume.Ray.trace w (fun x=>(x/v)^i)‖ ≤ η)
local notation "ε₁"=> spicesF G (r+fq) L' (V' x₀) K j
def seasoned (p:Signal j)(x γ α:ℝ) (k:ℕ)(i:Molecule S):= let m:= (1+H.shapeW i)^k; x *Real.exp (α*(coverNumber (radiusB x₀) (H.unionP i))) * V.pole.weight * (∏ l ∈ i.erase ((V.pole).turn.badge S), M.mouth γ p l) *m
include M hx he hv hm hy hU hc hr hh W' Y' D
set_option maxHeartbeats 400000 in
lemma earnsL (i:Molecule S) (hp:troupe T R Q.halo w₀ i) (hx':Healthy (Pressure.temp x₀) (H.unionP i) X.V)(hxP: (V.pole).turn.badge S∈i):
   Brush j (η * (seasoned M V p (ε₁) ν α (k+j) i)) 1 (fun x=>FullVolume.Ray.trace w (phraseS (fun t=>fence V X U₀ i t x))) s:=by
  let x₁(z:Air f G):= X.catastrophe (o.ξ/2) R.beta (blaze i)
  let μ':= (F.order G).prod X.dice; let I:= stampD (H:=H) i
  let c:=η*(Fold.charge j * FullVolume.Ray.Weigh.pattern j*(1+(L'*2^K+2*(r+fq)))^j)*Real.exp (α*coverNumber w₀ (H.unionP i))* (V.pole.weight*(∏ x∈i.erase ((V.pole).turn.badge S),M.meadow ν p x))*(1+H.shapeW i)^j
  let F' (z:F.Slice G × Air f G):= c*( (X.catastrophe (o.ξ/2) R.beta (blaze i)).indicator (fun z=>Flux.facescale I z^(K*j)) z.2)
  obtain ⟨hF,hM⟩ := M.fares W' hx hv he hm i
  have hv: Integrable F' μ':=(hF.comp_snd _).const_mul _
  let Ss(i':sun) (x:E) (t:F.Slice G × Air f G):= skyL M V X i i' x t (U₀:=U₀)
  let T₀ t x:= phraseS (fun t=>fence V X U₀ i t x) t; have hxQ(a:sun): T₀ a=fence V X U₀ i a:=funext fun t=> phrased _ a; have he' (a:sun): (ContDiffAt ℝ (↑j) (fence V X U₀ i a) s) ∧ ∀ k:ℕ,k≤j→ Integrable (JetF (Ss a) k s) μ' ∧ _:= cleaned M V D X hx he ‹X.χ=χ› hm hy hU i hp hx' a hxP
  obtain ⟨hY,hZ⟩:= fintrack (s:=s) (g:=T₀) w (fun i=> hxQ i|>.symm ▸ (he' i).1)
  refine ⟨hY,zero_le_one,fun n hn=>?_⟩; let f y:=∑ i∈w.support,w i • JetF (Ss i) n s y
  have hq y: Brush j (F' y) 1 (fun x=> FullVolume.Ray.trace w (phraseS (fun t=> skyL (U₀:=U₀) M V X i t x y))) s:=by
    have ht:= Mill.orbit M V D X hx he ‹X.χ=χ› hm hy hU hc hr i hp hxP hx' y
    refine ((ht.timber w η hh).trim).climb ?_ le_rfl; unfold F'
    by_cases hs:y.2 ∈ X.catastrophe (o.ξ/2) R.beta (blaze i); swap; · rw [Set.indicator_of_notMem hs,Set.indicator_of_notMem hs]; simp
    rw [Set.indicator_of_mem hs, Set.indicator_of_mem hs]
    have h₀:0≤ Fold.charge j:= (FullVolume.Ray.ink.pay_pos _).trans (le_max_left ..); have hb:= Y'.painter H.laws.data.funds.length_eq (H.unionP i) (Λ|>.full.2.2)
    let v:=I; let x':= Flux.facescale I y.2; let d:= 1+ H.shapeW i; have hx:1≤x':=(Flux.expenses ..).1; have hd:1≤d:= le_add_of_nonneg_right (H.positive_volume _); have hA : 0≤ η:= (norm_nonneg _).trans (hh 0)
    have hu:1+(L'*2^K*x'^K+(r+fq)*(2*H.shapeW i)) ≤ (1+(L'*2^K+2*(r+fq)))*d*x'^K:=by
      have hf:=one_le_pow₀ (n:=K) hx; have hv:= one_le_mul_of_one_le_of_one_le hd hf; have he:= (show d≤d*x'^K from le_mul_of_one_le_right (by linarith) hf); let A:=L'*2^K
      have hk:= mul_le_mul_of_nonneg_left (show x'^K ≤ d*x'^K from le_mul_of_one_le_left (zero_le_one.trans hf) hd) (show 0≤L'*2^K from mul_nonneg M.pole.pos (by positivity))
      nlinarith only [hv,hk,mul_le_mul_of_nonneg_left ((show H.shapeW i≤ d from le_add_of_nonneg_left zero_le_one).trans he) (add_nonneg (zero_le_one.trans M.pole.stencil.active) D.1)]
    let a:=V.pole.weight*(∏ x∈i.erase ((V.pole).turn.badge S),M.meadow ν p x); let p:= FullVolume.Ray.Weigh.pattern j; have hh':0≤ a:=mul_nonneg V.pole.profit (prod_nonneg fun _ _=> M.value_nn _); have hq:0≤p:=by unfold p FullVolume.Ray.Weigh.pattern; exact sum_nonneg fun i _=> zero_le_one.trans (Planned.AtomRegular.polar_one i)
    have hV:0≤price I G δ j:=mul_nonneg h₀ (pow_nonneg (by have he:=Λ|>.full.2.2; linarith) _); let hW:=Real.exp (α*coverNumber w₀ (H.unionP i)); have hc: price I G δ j ≤ Fold.charge j*hW:=mul_le_mul_of_nonneg_left hb h₀
    change p*(η*(price I G δ j*a))*(1+(L'*2^K*x'^K+(r+fq)*(2*H.shapeW i)))^j ≤ _
    apply (mul_le_mul (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hc hh') hA) hq) (pow_le_pow_left₀ ?_ hu j) (pow_nonneg ?_ _) ?_).trans
    · refine le_of_eq ?_; change _= c*x'^(K*j); unfold c; simp_rw [mul_pow,← pow_mul]; unfold p hW a d; ring
    all_goals have hg:0≤L':= M.pole.pos; have hv':0≤r:=zero_le_one.trans M.pole.stencil.active; have hv:0≤ r+fq:=add_nonneg hv' D.1; first|exact add_nonneg zero_le_one (add_nonneg (by positivity) (mul_nonneg hv (mul_nonneg (by norm_num) (H.positive_volume i)))) | unfold hW; positivity
  unfold normJ; rw [one_pow,mul_one]; change ‖iteratedFDeriv ℝ n (fun x=> FullVolume.Ray.trace w (fun t=>T₀ t x)) s‖≤ _; rw [hZ]
  swap; · assumption
  have hh i : Integrable (fun y:F.Slice G × Air _ G=> w i • JetF (Ss i) n s y) μ':= ((he' i).2 n hn).1.smul (w i)
  have hu' : (∑ z∈ w.support,w z • iteratedFDeriv ℝ n (T₀ z.val) s)= ∫ y, f y ∂ μ':= by -- binder change
    unfold f; rw [integral_finsetSum _ (fun i _=>hh i)]; apply sum_congr rfl; intro z hz; rw [integral_smul (w z) (JetF (Ss z) n s), hxQ z,(he' z|>.2 n hn).2]
  rw [hu']; apply (norm_integral_le_integral_norm _).trans; apply (integral_mono ((integrable_finsetSum _ fun _ _=> hh _).norm) hv (fun y=>?_)).trans
  · unfold F'; rw [integral_const_mul]; rw [integral_prod _ (hF.comp_snd _)] -- swap/comp
    dsimp only; rw [integral_const]; simp only [probReal_univ, one_smul]
    have ha:0≤c:= by
      unfold c
      have h':0≤FullVolume.Ray.Weigh.pattern j:=by unfold FullVolume.Ray.Weigh.pattern; exact sum_nonneg fun i _=>zero_le_one.trans (Planned.AtomRegular.polar_one i)
      have hx₁:0 ≤ η:=by apply (norm_nonneg _).trans (‹∀ i:ℕ,‖FullVolume.Ray.trace w (fun x=>(x/v)^i)‖≤η› 0)
      have hb:0≤ Fold.charge j := (FullVolume.Ray.ink.pay_pos _).trans (le_max_left ..); have hc:= H.positive_volume i; have hp:0≤ ∏ x∈i.erase ((V.pole).turn.badge S),M.meadow ν p x:=prod_nonneg fun _ _=> value_nn M _; have ht:= M.pole.pos; have ha:= M.pole.stencil.active;have hd:= D.1; have hg:=V.pole.profit; positivity
    refine le_trans (mul_le_mul_of_nonneg_left hM ha) (le_of_eq ?_); unfold seasoned spicesF c; simp only [← M.coal_norm, Daisy.flare_erase V.pole hxP, pow_add]; ring
  let Fm t x:= phraseS (fun t' => Ss t' x y) t
  have hf(i:sun): Fm i=fun z=> Ss i z y:=funext fun x=> phrased _ _
  have hx₁ (i':sun) : ContDiffAt ℝ (↑j) (Fm i'.val) s:= (Mill.orbit M V D X hx he ‹X.χ=χ› hm hy hU hc hr i hp hxP hx' y).smooth _ (i':sun).property
  have ht:= (fintrack (g:=Fm) w hx₁).2 n hn
  have he := ((hq y).order n hn); rw [one_pow,mul_one] at he; change ‖iteratedFDeriv ℝ n (fun x=> FullVolume.Ray.trace w (fun t=> Fm t x)) s‖≤_ at he; rw [ht] at he; simp_rw [hf] at he; exact he

end Mill
end YM.ConnectedActivityE6.Empire.Imago
