import YM.Next.STATIONARY.Loops.HessianMatch
import YM.Next.STATIONARY.Shape.Exchange





set_option autoImplicit false
/-!
# Luminous inherited-loop thickness, uniform row pitch. The tagged
 current of Γ comparison is NOT inserted here. C only via η input. -/
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Exterior Precision Wilson Bloch Laurent Matrix Finset Tree Asymptotics Audience
open scoped Topology ContDiff BigOperators
variable {G : Gauge} {P : Patch} {K : KernelChoices} {σ w C D A E τ η ε Ω : ℝ} {p : Clip} {R : PathData G} {n m : ℕ→Side}

section frost
variable (G)
private def glints : Fin 4→ Fin (1+1) := ![0,0,1,1]
abbrev Gaze := Ports 1 4

def iceBank (σ C E : ℝ) := ((Fintype.card (Breed 1 (Loc G 1)):ℝ)* Fintype.card Gaze*robinTax σ 1)*C^2 * E
variable {G} {Φ : Bridge G P}

def iceberg (U : Needle Gaze (Loc G 1) 1) (Φ : Bridge G P) : Picture G 1 := fun i j p=>
    let q := plotted p
    tunnels (roller glints) U q (fun a=> Φ (q a) *ᵥ Pi.single (j a,i a) 1)

lemma iceberg_price (U : Needle Gaze (Loc G 1) 1) (h : Cruise Φ 2 σ D) (hw : Dai U (inch P.L*σ) C) (hs : 0<σ) (hc : 0≤C) (i j) :
    Firm (surfHeight 1 σ) (inch P.L^2*iceBank G σ D C) (iceberg U Φ i j) := by
  let V (u : Space 1) (a : Fin (1+1)) := Φ (plotted u a) *ᵥ Pi.single (j a,i a) 1
  have ht := surf_gradient hs 1
  constructor
  · refine ⟨ht,fun p hp=> ?_,fun p hp z => ?_⟩
    · apply (tunnels_bill (roller glints) U hw hs (plotted p, V p) (surf_heat hs hp)).comp (f:=fun x=> (plotted x,V x)) p
      refine DifferentiableAt.prodMk (differentiableAt_pi.mpr fun i=> (platform_diffs i) p) (differentiableAt_pi.mpr fun i=> ?_)
      refine differentiableAt_pi.mpr fun k=> ?_; unfold V Matrix.mulVec dotProduct; exact DifferentiableAt.fun_sum fun x _=> ((h.1.shape (surf_heat hs hp _) k x).comp p ((platform_diffs _) p)).mul_const _
    have he a := projections_roll (show rolls p (p+reciprocal z) from ⟨z,rfl⟩) a
    change tunnels _ _ _ (V _)=tunnels _ _ _ (V _); rw [tunnels_twist _ _ he]; unfold V; simp_rw [h.1.shifts (he _) (surf_heat hs hp _)]
  intro p hp
  let l := roller (n:=4) glints
  have hr : 0≤ D := h.2.1
  let M i a := inch P.L^(1+(l i a).length)*D
  have ht a b j : Hearing (balcony _) 0 (fun z : Site P.L=> flight (plotted p b) (l a b) (V p b) (z,j)) (M a b) := by
    have hi : (l a b).length≤2 := by fin_cases b <;> simp [l,roller,tabsZ,List.finRange,glints]
    exact Hearing.sup (mul_nonneg (pow_nonneg (inch_pos _).le _) hr) (fun i=> h.2.2 _ hi _ (surf_heat hs hp b) _ _)
  have hT := tunnels_book l U hw hs (surf_heat hs hp) (V p) M ht (by simp) hc (fun a=> (needleCollapse (l a) 2 D P.L (by rw [show ∑ j,(l a j).length=4 from roller_extent ..])).le)
  exact hT.trans_eq (by unfold iceBank; ring)

lemma glacialStamp {U : Needle Gaze (Loc G 1) 1} {c f : Side} (S : StepData c f) {Φ : Bridge G S.patch} (h : Dai U (inch S.patch.L*σ) A) (hs : 0<σ) {W : Matrix (Body 1 f) (Body 1 c) ℝ} (he : Premise S W Φ) (hw : Poster σ Φ) {F : Link G f→ℝ} (ht : AnalyticAt ℝ F 0) (hp : Cargo (roller glints) U F) : Recorded (iceberg U Φ) (F∘uniformM W) 0 := by
  refine (record_exact ..).2 fun p i b=> ?_
  let L := uniformM (G:=G) W; let K := patron G W
  let z := (approached K).mulVecLin
  have hz x : axes (L x)=z (axes x) := by rw [show z (axes x)=_ from (show z (axes x)=axes (K *ᵥ x) from prom_vec ..), patron_fee]
  let k (p : Breed 1 Momentum) (j : Fin (1+1)) := Φ (p j)*ᵥ Pi.single (b j,i j) 1
  have hx (q : Breed 1 Momentum) (hQ : ∀ j,rolls (mon (p j)) (q j)) : noteAt (F∘ L) _ (glyph p i b)=if ∑ i,p i=0 then (Fintype.card (Site c):ℂ)*tunnels (roller glints) U q (k q) else 0 := by
    rw [note_comp L _ hz ht _]
    exact (congr_arg (noteAt F _) (show (fun j => z (glyph p i b j))=fun j=> poured S.ratio (p j) (k q j) from funext fun j=> tack_jack S Φ W he (hQ j) _)).trans (cargo_tick S.ratio h hp hQ hs _)
  unfold collected iceberg; split
  next he => exact (hx _ (fun j=> (ties he j).symm)).trans (if_pos he)
  next he => exact (hx (mon∘p) (fun j=> rolls.refl _)).trans (if_neg he)
end frost

section post
lemma bequest (G : Gauge) (σ D τ : ℝ) (hp : 0<σ) (hD : 0≤ D) (ht : 0<τ) : ∃ w C' : ℝ,0<w ∧ 0≤C' ∧ ∀ (m n : ℕ→Side), Tendsto (fun i=> (m i).val) atTop atTop →
    ∀ (P : Patch) (K : KernelChoices), P.Branches K G → ∀ (p : Clip) (B T : Bed) (R : PathData G) (M : Eye (Loc G 1) (Acts G P)) (Y : Spark (Loc G 1) G P) (Q : PostCard R p P K M Y m n) (η ξ ε Ω A Λ v : ℝ) (X : TicketPost Q η B T) (Φ : Bridge G P), R.Bounds p τ A Λ → 0≤Λ → Cruise Φ 2 σ D → (∀ i, Premise (Q.ship.boot i) (X.mat i) Φ) →
      T.metric.strip ξ Ω → 0<ξ → B.metric.strip (inch P.L*σ) v → (∀ i, Floor B p i ε v) → 0<ε → inch P.L*σ ≤ w →
    ∃ L : Picture G 1,(∀ i, Recorded L (burnished (X.tree i) R (X.graph i)) 0) ∧ ∀ i j, Firm (surfHeight 1 σ) (inch P.L^2 * (Λ*C')) (L i j) ∧ Rays 4 (L i j ∘ axes) := by
  obtain ⟨w,P,h,hP,H⟩ := windTwin (G:=G) 4 glints ht
  let v := |reflectBill 1 τ * inheritRate τ|
  let E := iceBank G σ D (v*P)
  have he : 0 ≤ v := abs_nonneg _
  have hc' : 0≤ E := by unfold E iceBank robinTax; positivity
  refine ⟨w,E,h,hc',fun m n hm S K hS p B T R U Y Q η ξ ε Ω A Λ v₀ X Φ hv hx hu hQ hT hξ hb hF hε hH => ?_⟩
  obtain ⟨h₁,h₂⟩ := filing_ready R hv
  have h₁ i j : Firm τ (Λ*v) (filing R i j) ∧ Rays 4 (filing R i j ∘ axes) := ⟨(h₁ i j).1.mono ht le_rfl (mul_le_mul_of_nonneg_left (le_abs_self _) hx),(h₁ i j).2⟩
  have he₀ i : Recorded (filing R) (turnSeries (m:=n i) R.loop) 0 := h₂ _
  obtain ⟨a,ha,hα⟩ := H _ (mul_nonneg hx he) _ h₁
  let L := iceberg a Φ
  have hΛ : 0≤Λ*v*P := by positivity
  have h : Dai a (inch S.L*σ) (Λ*v*P) := fun u i=> (ha u i).mono hH le_rfl
  have hl i j : Firm (surfHeight 1 σ) (inch S.L^2*(Λ*E)) (L i j) := by convert iceberg_price a hu h hp hΛ i j using 1; unfold E iceBank; ring
  have hz (i : ℕ) : Pointwise (turnSeries (m:=n i) R.loop) := stain_ink _ ht hv.two (fun i=> (hv.invariant i).1)
  have hr i : Recorded L ((turnSeries (m:=n i) R.loop)∘ uniformM (G:=G) (X.mat i)) 0 := glacialStamp (Q.ship.boot i) h hp (hQ i) hu.1 (hz i).analytic (spooling ‹0<w› hα ha (he₀ _))
  have hm' : Tendsto (fun i=> (n i).val) atTop atTop := tendsto_atTop_mono (fun i=> (show (m i).val ≤ (n i).val from by rw [Q.ship.binds]; exact Nat.le_mul_of_pos_right _ S.L.pos)) hm
  have hs := withdrew hm' (tendsto_const_nhds (x:=(0:ℝ))) (fun i j => (h₁ i j).1) (fun i => by simpa only [mul_zero] using (he₀ i)) (fun i=> (hz i).analytic) (fun i=> (hz i).stained) (fun i=> (hz i).guard) (fun i j h _=> (rays_jet (hz i).analytic _).mp (turns_low R.loop ht hv.two (m:=n i)) _ h)
  have hh q (hv : star q=q) := carry_plan Q.ship hu.1 hp (fun i j=> (h₁ i j).1) hl hQ (fun i => (hz i).analytic) (fun i => by rw [mul_zero]; exact he₀ i) (fun i=> by rw [mul_zero]; exact hr i) (tendsto_const_nhds (x:=(0:ℝ))) (tendsto_const_nhds (x:=(0:ℝ))) hm hv
  have hL := inkA_rays (weaken_cop hp hu.1 hb (mul_pos (inch_pos _) hp) hT hξ hF hε hs.wall (fun i j=> (h₁ i j).1) (fun i hv=> (actor_duo Q.ship hξ hT hp hb hp hu.1 hm hQ X.sworn hv).1) hh (le_rfl:4≤4) (raysA_ink fun i j=>(h₁ i j).2))
  refine ⟨L,fun i=> (record_exact ..).2 (fun p b j=> ?_),fun i j => ⟨hl i j,hL i j⟩⟩
  refine Eq.trans ?_ ((record_exact ..).1 (hr i) p b j); unfold noteAt beat
  rw [show iteratedFDeriv ℝ (1+1) (burnished _ _ _) _= _ from inherited_le (X.decor i) hS hv (t:=Q.tags i) _ (X.guards i)]
end post
end YM.Stationary
end

/-!
# Loop path lift and alpha accounting from common drawings. Width
independent of scales and alpha; amplitude estimates still paid by
the supplier. The drawing f is *only* for the det/Jac (no inherited
loop); Λ allowed on the latter, and its leading Ray test then enters as
an explicit guard. -/
noncomputable section
namespace YM.Stationary
open Function Filter Finset Lattice RG Wilson Exterior Precision Bloch Laurent
open Matrix (transpose mulVec of)
open scoped Matrix Topology ContDiff BigOperators InnerProductSpace Matrix.Norms.Frobenius
variable {G : Gauge} {m : ℕ → Side}

lemma point_quiet (hG : G.Simple) {m : Side} {F : Link G m → ℝ} (h : Pointwise F) : Quiets F 2 := by
  have he : fderiv ℝ F 0=0 := by
    apply ContinuousLinearMap.ext; intro i
    exact oneFlag hG (fderiv ℝ F 0) (fun u v => by rw [← tincture u]; exact chain_fixed _ (h.stained u) h.analytic.differentiableAt v) i
  intro i hi hp; rw [show i=1 by omega]; ext1 v; simp [he]
lemma point_receipt (hG : G.Simple) {m : ℕ→Side} {F : ∀ i, Link G (m i)→ℝ} {σ A : ℝ} {ε : ℕ→ℝ} {f : Picture G 1}
    (hm : Tendsto (fun i => (m i).val) atTop atTop) (he : ∀ i j,Firm σ A (f i j))
    (hε : Tendsto ε atTop (𝓝 0)) (hp : ∀ i,Recorded f (F i) (cents (m i)*ε i)) (h : ∀ i, Pointwise (F i)) : TributeColor f σ A Universal := tributing hm he hε hp (fun i => (h i).analytic) (fun i => (h i).guard) (fun i => (h i).stained) (fun i => point_quiet hG (h i)) (fun i s _ => (h i).rotate s)

def Bs (G : Gauge) (f : ℕ → Atom G 2) := ∀ (i : Fin 2→PlaqAxes) (x : Fin 2→G.ColorIndex) (R : PathData G), R.loop=f →
      HasSum (R.loop_coeff i x) 0 ∧ ∀ l : Axis, HasSum (fun n => R.loop_coeff i x n * ↑((((f n).leg 1).offset l-((f n).leg 0).offset l : ℤ))) (0:ℝ)

lemma reach_symbol (G : Gauge) (hG : G.Simple) (σ : ℝ) (hs : 0<σ) :
    ∃ η K : ℝ, 0<η ∧ η ≤ σ ∧ 0≤K ∧ ∀ (m : ℕ→Side), Tendsto (fun i => (m i).val) atTop atTop →
    ∀ U : ∀ i, Link G (m i)→ℝ, ∀ W T : ∀ i, Link G (m i)→ℝ,
    ∀ (A B M : ℝ) (ε : ℕ → ℝ) (f g : Picture G 1) (R : FaceRow) (i : G.ColorIndex),
      0≤A → 0≤B → 0≤M → Tendsto ε atTop (𝓝 0) → R.strip σ M → R.read 0=1 →
      (∀ i,Pointwise (U i) ∧ Pointwise (W i) ∧ Pointwise (T i)) →
      (∀ i j,Firm σ A (f i j) ∧ Firm σ B (g i j) ∧ Rays 4 (g i j ∘ axes)) →
      (∀ i,Recorded (slots R G) (T i) 0 ∧ Recorded f (U i) (cents (m i)*ε i) ∧ Recorded g (W i) 0) →
    ∃ Q : ℕ → Atom G 2,
      let a := alphaPay i f
      AtomWall Q η ((A + |a| * bedCharge σ M+B)*K) ∧ Bs G Q ∧
      ∀ i, aperture (cents (m i)*ε i) (turnSeries (m:=m i) Q) (U i-a • T i + W i) 1 := by
  obtain ⟨η,C,hh,hη,hC,H⟩ := veins G σ hs
  refine ⟨η,C*inkCost G 1 η,hh,hη,mul_nonneg hC (inkCost_nonneg ..),fun m hm U W T A B M ε f g R i hA hB hM he hR hg hP hF hu => ?_⟩
  let a := alphaPay i f
  let V := fun i => U i-a • T i
  let p := f-(a:ℂ) • slots R G
  let u := A + |a| * bedCharge σ M
  have hE (i) : Recorded p (V i) (cents (m i)*ε i) :=
    Recorded.less (F:=U i) (H:=a • T i) (hP i).1.analytic (((hP i).2.2.coin a).analytic) (hu i).2.1
      ((hu i).1.weigh a (hP i).2.2.analytic)
  have hT i j : Firm σ u (p i j) := by
    have hh := ((hF i j).1).sub ((Firm.const (α:=Keys 1) hs (a:ℂ)).mul (slots_cost hs hR i j))
    rw [Complex.norm_real, Real.norm_eq_abs] at hh; exact hh
  have hV (i) : Pointwise (V i) := (hP i).1.sub ((hP i).2.2.coin a)
  have h' := point_receipt hG hm (fun i j => (hF i j).1) he (fun i => (hu i).2.1) (fun i => (hP i).1)
  have hp := point_receipt hG hm hT he hE hV
  have hx : leapTip p (step (0:Axis)) 1 ![i,i]=0 := subtract_fee i h' hR hs hg rfl
  have hw k j := hp.vanish hG 1 0 (by decide) i hx k j
  have hF' i j : Firm σ (u+B) ((p+g) i j) := (hT i j).add (hF i j).2.1
  have hz i := Recorded.both (hV i).analytic ((hP i).2.1).analytic (hE i) (hu i).2.2
  have H' := point_receipt hG (F:=V+W) hm hF' he hz (fun i => (hV i).add (hP i).2.1)
  obtain ⟨Q,hQ,hO⟩ := H (u+B) 2 (p+g) (by unfold u; have hp := bedCharge_nonneg (σ:=σ) hM; positivity) H'.toFeatures (fun i j => (hw i j).add (hF i j).2.2)
  obtain ⟨hi,hb⟩ := artery_funded hQ
  refine ⟨issue Q,⟨by rw [← mul_assoc]; exact hi,hb⟩, fun i x R hv => issue_normal hQ.price hh hO R hv i x,?_⟩
  intro i
  have hh' := (hV i).add (hP i |>.2.1)
  exact colors_align _ hh'.analytic hh'.lights (p+g) Q hQ hh (hz i)
end YM.Stationary
end

/-! # Comparison in literal real wave tests, including unordered momenta
and anchor sign. No uniform claim on determinant discrepancy from truncating
the (yet to be computed) period-limit. -/
noncomputable section
namespace YM.Stationary
open Function Filter Finset Lattice RG Wilson Exterior Precision Bloch Laurent Tree
open Matrix (transpose mulVec of)
open scoped Matrix Topology ContDiff BigOperators InnerProductSpace Matrix.Norms.Frobenius
variable {G : Gauge} {m : Side} {σ A : ℝ}

def pew (p : Site m) (v : TypeFace 1 → G.ColorIndex→ℂ) := (arm G m 1).symm (wave p v)
lemma pew_plane (p : Site m) (v : TypeFace 1 → G.ColorIndex→ℂ) :
    axes (pew p v)=(1/2:ℂ) • tune p (Function.uncurry v)+(1/2:ℂ) • tune (-p) (star (Function.uncurry v)) := by
  let A := tune p (Function.uncurry v)
  have he : tune (-p) (star (Function.uncurry v))=star A := by
    funext x
    simp only [A,tune, Pi.star_apply,star_mul]; rw [cell_duality (-p),cell_inverse,Complex.star_def,cell_bar,cell_duality]; ring
  rw [he]
  ext1 x; change ↑((A x).re) = (1/2:ℂ)*(A x)+(1/2:ℂ)*star (A x); rw [Complex.star_def, ← mul_add,Complex.add_conj]; push_cast; ring

def waveBank (G : Gauge) := 2*((Fintype.card (Loc G 1):ℝ) * Fintype.card (Loc G 1))

variable {F H : Link G m → ℝ} {ε : ℝ}
lemma live_wave (hp : aperture ε F H 1) (_hε : 0≤ε) (p q : Site m) (u v : TypeFace 1 → G.ColorIndex → ℂ) (hu : ∀ i j, ‖u i j‖≤1) (hv : ∀ i j, ‖v i j‖ ≤ 1) :
    |iteratedFDeriv ℝ 2 F 0 ![pew p u,pew q v]-iteratedFDeriv ℝ 2 H 0 ![pew p u,pew q v]| ≤ waveBank G*ε := by
  let a := noteAt F 2 - noteAt H 2
  let A := a.curryLeft
  have he (x y : Site m) (u v : Loc G 1) : ‖a ![relay x u, relay y v]‖ ≤ ε := by
    have h : glyph (![x,y]) (![u.2,v.2]) ![u.1,v.1]= ![relay x u,relay y v] := by ext1 i; fin_cases i <;> rfl
    have hp := hp ![x,y] ![u.2,v.2] ![u.1,v.1]; dsimp only at hp; rw [h] at hp; exact hp
  let c := (Fintype.card (Loc G 1):ℝ)*Fintype.card (Loc G 1)*ε
  have hh (x y : Site m) (U V : Phase (Loc G 1)) (hU : ∀ i,‖U i‖≤1) (hV : ∀ i,‖V i‖≤1) : ‖a ![tune x U,tune y V]‖ ≤ c := by
    have hz (w : Site m) (u : Phase (Loc G 1)) : tune w u=∑ j,u j • relay w j := by
      funext i; rw [Finset.sum_apply]; simp [tune,relay,Pi.single_apply,mul_comm]
    let f (i : Fin 2) (j : Loc G 1) := (![U,V] i j) • relay (![x,y] i) j
    have hh : ![tune x U,tune y V]=(fun i => ∑ j,f i j) := by
      ext1 i; fin_cases i
      · exact hz x U
      exact hz y V
    rw [hh,MultilinearMap.map_sum (g:=f)]
    calc
    _ ≤ _ := norm_sum_le _ _
    _ ≤ ∑ _ : Fin 2 → Loc G 1, ε := by
      refine sum_le_sum fun i _ => ?_
      rw [show a (fun j => f j (i j)) = (∏ j,![U,V] j (i j)) • a (fun j => relay (![x,y] j) (i j)) from a.map_smul_univ _ _,
        show a (fun j => relay (![x,y] j) (i j))=a ![relay x (i 0),relay y (i 1)] from congr_arg _ (funext fun j => by fin_cases j <;> rfl), norm_smul, Fin.prod_univ_two,norm_mul]
      exact (mul_le_mul (mul_le_one₀ (hU _) (norm_nonneg _) (hV _)) (he ..) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
    _ = _ := by simp [sq,c]
  let U := axes (pew p u); let V := axes (pew q v); let u' := Function.uncurry u; let v' := Function.uncurry v
  have hU i : ‖u' i‖≤1 := hu ..
  have hV i : ‖v' i‖≤1 := hv ..
  have hu' i : ‖star u' i‖≤1 := by rw [Pi.star_apply,norm_star]; exact hU i
  have hv' i : ‖star v' i‖≤1 := by rw [Pi.star_apply,norm_star]; exact hV i
  let L := (![tune p u',tune (-p) (star u')]:Fin 2 → Phase (Lines G m 1))
  let K := (![tune q v',tune (-q) (star v')]:Fin 2 → Phase (Lines G m 1))
  let l (i j : Fin 2) := (1/2:ℂ) • ![L,K] i j
  have hK (j i) : ‖a ![L j,K i]‖ ≤ c := by
    fin_cases j <;> fin_cases i
    · exact hh p q u' v' hU hV
    · exact hh p (-q) _ _ hU hv'
    · exact hh (-p) q _ _ hu' hV
    exact hh (-p) (-q) _ _ hu' hv'
  have hx : ‖a ![U,V]‖ ≤ c := by
    rw [show ![U,V]=(fun i => ∑ j : Fin 2, l i j) by
      ext1 i; fin_cases i <;> rw [Fin.sum_univ_two]
      · exact pew_plane p u
      exact pew_plane q v
    ,MultilinearMap.map_sum (g:=l)]
    calc
      _ ≤ _ := norm_sum_le _ _
      _ ≤ ∑ _ : Fin 2→ Fin 2, (1/2:ℝ)^2*c := by
        apply Finset.sum_le_sum; intro i _
        rw [show a _=(∏ _ : Fin 2,(1/2:ℂ)) • a (fun j : Fin 2 => ![L,K] j (i j)) from a.map_smul_univ (fun j : Fin 2 => (1/2:ℂ)) (fun j : Fin 2 => ![L,K] j (i j)), show (fun j : Fin 2 => ![L,K] j (i j))=![L (i 0),K (i 1)] from funext (fun j => by fin_cases j <;> rfl)]
        rw [norm_smul, prod_const, card_univ,Fintype.card_fin, norm_pow,show ‖(1/2:ℂ)‖=(1/2:ℝ) by norm_num]; gcongr; exact hK ..
      _ = _ := by simp; ring
  let f (F : Link G m→ℝ) := iteratedFDeriv ℝ 2 F 0 ![pew p u,pew q v]
  have hg (F : Link G m→ℝ) : noteAt F 2 ![U,V]=(1/2:ℝ) • ((f F:ℝ):ℂ) := by
    rw [show ![U,V]=axes ∘ ![pew p u, pew q v] from funext (fun i => by fin_cases i <;> rfl),note_real,Tensor.coeff]; norm_num [Nat.factorial,f]
  unfold a at hx; simp only [_root_.sub_apply,hg, ← smul_sub, ← Complex.ofReal_sub,norm_smul, Complex.norm_real] at hx
  change |f F-f H| ≤ 2*_ * ε
  change ‖(1/2:ℝ)‖*‖f F-f H‖ ≤ _ at hx; rw [Real.norm_eq_abs (f F-f H), Real.norm_of_nonneg (by norm_num : 0 ≤ (1/2:ℝ))] at hx
  rw [mul_assoc]; change _ ≤ 2*c; linarith
end YM.Stationary
end

/-!
# To `retains` on the chosen period. Input epsilon, includes census
on OUTPUT lattice. Needn't allocate unit on warm-first alpha tests.
Pay for any U of same row/atom family in `kinetic_pipe`; loop labels
fixed (not zeroing). Other Choices SAME path. -/
noncomputable section
namespace YM.Stationary
open Function Filter Finset Lattice RG Wilson Exterior Precision Bloch Laurent Tree
open Matrix (transpose mulVec of)
open scoped Matrix Topology ContDiff BigOperators InnerProductSpace Matrix.Norms.Frobenius
variable {G : Gauge} {m n c f : Side} {S : StepData c f}

section comparison
variable {ε σ τ A B Λ Δ κ μ η α : ℝ} {P : ChartRatio G} {p q : Clip} {U T : PathData G} {F : Forest S.ratio}
    {ρ : Bid.Dir G c → AxisChart G F}
lemma wired_wave {f : fieldDir G c 1 → ℝ} (h : ContDiffAt ℝ ω (f ∘ arm G c 1) 0) (p q : Site c) (u v) :
    iteratedFDeriv ℝ 2 f 0 ![wave p u,wave q v] = iteratedFDeriv ℝ 2 (f ∘ arm G c 1) 0 ![pew p u,pew q v] := by
  let K := arm G c 1
  have ht : iteratedFDeriv ℝ 2 ((f ∘ K) ∘ K.symm.toContinuousLinearMap) 0 ![wave p u,wave q v]=_ :=
    wired K.symm.toContinuousLinearMap (show AnalyticAt ℝ (f ∘ K) (K.symm.toContinuousLinearMap 0) by rw [map_zero]; exact h.analyticAt) 2 ![wave p u,wave q v]
  rw [show (f ∘ K) ∘ K.symm.toContinuousLinearMap = f by funext v; simp only [Function.comp_apply,ContinuousLinearEquiv.coe_coe,K.apply_symm_apply],map_zero] at ht
  rw [ht,show K.symm.toContinuousLinearMap ∘ (![wave p u,wave q v]:Fin 2→fieldDir G c 1)=![pew p u,pew q v] from funext (fun i => by fin_cases i <;> rfl)]
lemma haze_draft (U : PathData G) (x : ℝ) (he : U.Bounds p σ A Λ) :
    ContDiffAt ℝ ω (draft (c:=c) x U p) 0 := by
  let P := x • inputSeries p U (m:=c); let Q := turnSeries U.loop (m:=c)
  have hp : draft x U p=P ∘ (arm G c 1).symm+ Q ∘ (arm G c 1).symm := by
    funext v; simp only [Pi.add_apply,Function.comp_apply,P,Q,turnSeries,inputSeries,Pi.smul_apply,input,(arm _ _ _).apply_symm_apply,draft]; rfl
  rw [hp]; apply ContDiffAt.add
  · have hh : AnalyticAt ℝ P ((arm G c 1).symm 0) := by rw [map_zero]; exact ((stain_knit U p he).coin x).analytic
    exact hh.contDiffAt.comp (f:= (arm G c 1).symm) _ (arm G c 1).symm.contDiff.contDiffAt
  have hh : AnalyticAt ℝ Q ((arm G c 1).symm 0) := by rw [map_zero]; exact turns_analytic _ he.width he.two
  exact hh.contDiffAt.comp (f:= (arm G c 1).symm) _ (arm G c 1).symm.contDiff.contDiffAt

lemma draft_pipe (t : S.Choices) (bh : Critical F p U ρ) (bs : S.patch.Branches S.kernel G)
    (hu : U.Bounds p σ A Λ) (ht : T.Bounds q τ B Δ)
    (hz : PriceGap F p U η) (hp : 0<η) (hv : 0<μ) (hA : LocalRatio P) (he : 0 ≤ ε)
    (hr : aperture (cents c*ε) (turnSeries T.loop) ((honorarium F t μ p U ρ) - α • (inputSeries q T)+ (burnished F U ρ)) 1)
    (Θ y Ω : ℝ) (hx : waveBank G * ε ≤ Θ*Ω * Real.exp (-y*c.val)) : FiniteBound F U T p q α P ρ Θ y Ω := by
  have hb := haze_draft (c:=c) T α ht
  refine ⟨Work.F05.hessian_pos hp hz bh, fun a => born hu bh hz hp hA a,hb,?_⟩
  intro k i j u v heU heV L
  have HH := (coin_tag bh bs hu t k hz hp hv hA).2
  let C := honorarium F t μ p U ρ
  let M := burnished F U ρ
  let F' := (arm G c 1)
  let K := α • (inputSeries q T (m:=c))
  let Q := (turnSeries T.loop (m:=c))
  have hm : ContDiffAt ℝ ω (thermal F k p U ρ P ∘ F') 0 := (show ContDiffAt ℝ ω _ (F' 0) from
      (by rw [map_zero]; exact born hu bh hz hp hA k)).comp _ F'.contDiff.contDiffAt
  have hn : ContDiffAt ℝ ω (draft α T q ∘ F') 0 := ContDiffAt.comp (g:=draft α T q) (f:=F') _ (by rw [map_zero]; exact hb) F'.contDiff.contDiffAt
  have hT : thermal F k p U ρ P ∘ F'=ᶠ[𝓝 0] (C+M) := by
    filter_upwards [HH, tribute bh bs hu hz hp hv k hA] with x he h
    change _=honorarium F t _ _ _ _ x + _
    rw [he,add_comm]; exact h.2
  have hd : draft α T q ∘ F' = K+Q := rfl
  have hk : ContDiffAt ℝ ω K 0 := ((stain_knit T q ht).coin α).analytic.contDiffAt
  have hq : AnalyticAt ℝ Q 0 := turns_analytic _ ht.width ht.two
  have H := campaign bh bs hu t hz hp hv hA
  have Hm : ContDiffAt ℝ 2 M 0 := H.2.2.analytic.contDiffAt
  have Hc : ContDiffAt ℝ 2 C 0 := H.2.1.analytic.contDiffAt
  have hy := live_wave hr (mul_nonneg cents_pos.le he) i j u v heU heV
  unfold L
  rw [wired_wave hm,wired_wave hn, show iteratedFDeriv ℝ 2 _ _= _ from (hT.iteratedFDeriv ℝ 2).eq_of_nhds,
    show iteratedFDeriv ℝ 2 _ _=_ from congr_arg (iteratedFDeriv ℝ 2 · 0) hd]
  rw [iteratedFDeriv_add_apply Hc Hm, iteratedFDeriv_add_apply (hk.of_le le_top) hq.contDiffAt]
  change |iteratedFDeriv ℝ 2 Q 0 _ - iteratedFDeriv ℝ 2 ((C-K)+M) 0 _| ≤ _ at hy
  rw [iteratedFDeriv_add_apply (show ContDiffAt ℝ 2 (C-K) 0 from Hc.sub (hk.of_le le_top)) Hm,iteratedFDeriv_sub_apply Hc (hk.of_le le_top)] at hy
  let W := ![pew i u,pew j v]
  simp only [_root_.add_apply] at *; simp only [_root_.sub_apply] at hy
  trans waveBank G*(cents c* ε)
  · rw [abs_sub_comm]
    change |_ + iteratedFDeriv ℝ 2 Q 0 W- _| ≤ _
    rw [show iteratedFDeriv ℝ 2 K 0 W + _- _ = iteratedFDeriv ℝ 2 Q 0 W-(iteratedFDeriv ℝ 2 C 0 W-iteratedFDeriv ℝ 2 K 0 W+iteratedFDeriv ℝ 2 M 0 W) from ?_]; exact hy
    abel
  calc
    _ = cents c * (waveBank G*ε) := mul_left_comm ..
    _ ≤ _ := (mul_le_mul_of_nonneg_left hx (cents_pos.le)).trans_eq (by simp [cents,mul_assoc])
end comparison
end YM.Stationary
end

/-!
# Uniform WP from phase estimates. Before the β-dependent supplies. Metric
stamp complied with also on the new paths at all given period numbers.
Not assuming coefficients emitted adhere to the input bounds; outputs a path.
Widths choose jointly before learning Φ/graph prices. -/
noncomputable section
namespace YM.Stationary
open Function Filter Finset Lattice RG Wilson Exterior Precision Bloch Laurent Tree
open Matrix (transpose mulVec of)
open scoped Matrix Topology ContDiff BigOperators InnerProductSpace Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f} {F : Forest S.ratio}

section earth
variable {ρ : Bid.Dir G c → AxisChart G F} {p q : Clip} {U T : PathData G} {B C : Bed}
lemma violet (hs : Bid.Larger (G:=G) S) (hC : Critical F p U ρ) (hk : Bid.HeatG F p U ρ C) {x y z w σ D Λ τ D' Λ' : ℝ}
    (hp : U.Bounds p σ D Λ) (hu : Attached B U) (hm : Floor B p f x y) (hb : Bid.Sworn B f G)
    (ht : T.Bounds q τ D' Λ') (hv : Attached C T) (ha : Floor C q c z w) (hw : Bid.Sworn C c G) (t : S.Choices) :
    Rays 3 (victory F t p U ρ-inputSeries q T) := by
  have he := low_columns ht hv ha hw
  let g := inputSeries q T (m:=c)
  have hy : Pointwise g := stain_knit T q ht
  have hr := Work.F04.half_pairing g hy.analytic.contDiffAt
  have hh' x y : fderiv ℝ (fderiv ℝ g) 0 x y=Bid.gaugeFiscal C (arm G c 1 x) (arm _ _ _ y) :=
    (by refine Eq.trans ?_ (he.2.2 x y); rw [iteratedFDeriv_two_apply]; rfl)
  simp_rw [hh'] at hr
  let u := fun x : Bid.Dir G c => tested F t p U x (ρ x)
  have hz : ContDiffAt ℝ ω u 0 := (hk t).1
  let L := (arm G c 1).toContinuousLinearMap
  have hk0 : L 0=0 := map_zero _
  have hϕ : SameJet 2 u _ := hk t
  have hd : ContDiffAt ℝ ω (victory F t p U ρ) 0 := (show ContDiffAt ℝ ω u (L 0) from hk0.symm ▸ hz).comp _ L.contDiff.contDiffAt
  have hx : iteratedFDeriv ℝ 2 (victory F t p U ρ) 0=iteratedFDeriv ℝ 2 g 0 := by
    rw [hr.2.2]; ext1 v
    let M := fun x : Bid.Dir G c => (1/2:ℝ)*Bid.gaugeFiscal C x x
    change iteratedFDeriv ℝ 2 (u ∘ L) _ _=iteratedFDeriv ℝ 2 (M ∘ L) _ _
    rw [wired L (by rw [map_zero]; exact hz.analyticAt), wired L (by rw [map_zero]; exact hϕ.2.1.analyticAt),map_zero,hϕ.2.2]
  have ho := Work.F03.answer _ _ _ S hs F B p U _ _ _ _ _ hm hp hu hb (Work.F02.answer _ _ _ _ _ _ hp)
  let f := uncurry <| tested F t p U
  let v := fun x => (L x,ρ (L x))
  have hn : v 0=0 := by unfold v; simp only [map_zero,hC.1]; rfl
  have hD : ContDiffAt ℝ ω v 0 := L.contDiff.contDiffAt.prodMk ((show ContDiffAt ℝ ω ρ (L 0) from hk0.symm ▸ hC.2.1).comp _ L.contDiff.contDiffAt)
  have ht' : victory F t p U ρ 0=0 := (congr_arg f hn).trans (ho.2 t).1
  have ha : fderiv ℝ (victory F t p U ρ) 0=0 :=
    (Work.F03.hessian_comp hn (f:=f) ((ho.1 t).of_le le_top) (hD.of_le le_top) (ho.2 t).2.1).1
  apply (rays_jet (hd.analyticAt.sub hy.analytic) _).2; intro i hi; interval_cases i
  · ext; simp [ht',show g 0=0 from he.1]
  · ext1 v; rw [iteratedFDeriv_one_apply, fderiv_sub (hd.differentiableAt (by simp)) (show DifferentiableAt ℝ g 0 from hy.analytic.differentiableAt),ha,show fderiv ℝ g 0=0 from he.2.1, sub_zero]; rfl
  rw [iteratedFDeriv_sub_apply (hd.of_le le_top) hy.analytic.contDiffAt, hx,sub_self]
lemma achieved (hs : S.patch.Branches S.kernel G) (hc : Critical F p U ρ) {σ D Λ η A Λ' b : ℝ} (hp : U.Bounds p σ D Λ) (ht : T.Bounds q η A Λ')
    (r : S.Choices) (hu : PriceGap F p U b) (hb : 0<b) (hv : Rays 5 (victory F r p U ρ-intended q T)) :
    ClassicalMatch F p q U T ρ := by
  obtain ⟨P,hP⟩ := LocalH.actual G
  intro i hi t
  have hp' := (campaign hc hs hp t hu hb (μ:=1) zero_lt_one hP).1
  refine matched (G:=G) (m:=c) (p:=fun x => tested F t p U x (ρ x)) (q:=fun x => mainTerm q T (represent x)) hp'.analytic (strain q T ht).analytic (n:=5) ?_ i (by omega)
  intro x
  have he := (coin_tag hc hs hp t r hu hb zero_lt_one hP).1
  exact (hv x).congr' (by filter_upwards [(along x).eventually he] with a ha; exact congr_arg (·-intended q T (a • x)) ha.symm) <| EventuallyEq.rfl
end earth

section all
variable {c f : ℕ→Side} (m : ℕ→Side)
/-- All periods assembler. σ width on phase INPUT; scene gap price η
    quantifiers not provided. Using fixed K stamps and waiting for geometry;
    Price not tied to calendar λ except later. -/
theorem color_pipe (G : Gauge) (hG : G.Simple) (σ w M Z : ℝ) (hs : 0<σ) (hw : 0<w) (hz : 0≤Z) :
    ∃ s K D : ℝ, 0<s ∧ s≤min σ w ∧ 0≤K ∧ 0≤D ∧ ∀ (c f : ℕ → Side), Tendsto (fun i => (c i).val) atTop atTop →
    ∀ (S : ∀ i, StepData (c i) (f i)) (F : ∀ i, Forest (S i).ratio) (t : ∀ i, (S i).Choices), (∀ i, Bid.Larger (G:=G) (S i)) →
    ∀ (p q : Clip) (B C : Bed) (U : PathData G) (ρ : ∀ i, Bid.Dir G (c i) → AxisChart G (F i)) (P : ChartRatio G) (μ τ A Λ η x y z u : ℝ), q.direct ≤ Z → LocalRatio P → 0<μ → 0<η →
      U.Bounds p τ A Λ → Attached B U → (∀ i, PriceGap (F i) p U η ∧ Critical (F i) p U (ρ i) ∧ Bid.HeatG (F i) p U (ρ i) C) →
      (∀ i, Floor B p (f i) x y ∧ Bid.Sworn B (f i) G) → (∀ n : Side, Floor C q n z u) → (∀ i, Bid.Sworn C (c i) G) →
      C.metric.strip w M → C.roots.strip w M →
    ∀ (L α : Picture G 1) (X Φ R : ℝ) (ε : ℕ → ℝ) (i : G.ColorIndex), Tendsto ε atTop (𝓝 0) → (∀ i, 0 ≤ ε i) → 1≤X →
      HasRecord (fun i=> victory (F i) (t i) p U (ρ i)) σ X 2 → HasRecord (fun i=> victory (F i) (t i) p U (ρ i)) σ X 3 →
      (∀ i j,Firm σ Φ (α i j) ∧ Firm σ R (L i j) ∧ Rays 4 (L i j ∘ axes)) →
      (∀ i, Recorded α (honorarium (F i) (t i) μ p U (ρ i)) (cents (c i)*ε i) ∧ Recorded L (burnished (F i) U (ρ i)) 0) →
    ∃ T : PathData G,
      T.row=rowPath C ∧ Attached C T ∧ (∀ s' A' Λ', 0<s' → s'≤s → rowPrice w M ≤ A' → X*K ≤ A' →
        (Φ + |alphaPay i α| * bedCharge (min σ w) M+R)*D ≤ Λ' → T.Bounds q s' A' Λ') ∧
      (∀ i, ClassicalMatch (F i) p q U T (ρ i)) ∧ ∀ j (Θ g Ω : ℝ), waveBank G*ε j ≤ Θ*Ω*Real.exp (-g * (c j).val) →
        FiniteBound (F j) U T p q (alphaPay i α) P (ρ j) Θ g Ω := by
  let s := min σ w
  have hS : 0<s := lt_min hs hw
  obtain ⟨a,K,ha,h₁,k,I⟩ := assembly G σ w M Z hs hw hz
  obtain ⟨b,D,hb,h₂,d,Q⟩ := reach_symbol G hG s hS
  refine ⟨min a b,K,D,lt_min ha hb,(min_le_right ..).trans h₂,k,d,?_⟩
  intro c f hm S F t h p q B C U ρ P μ τ A Λ η x y z u ht hP hg hη hu he H HY hF hx hW hR L α X Φ R ε i hε hv hX hh ho hK hz
  let f0 (i) := victory (F i) (t i) p U (ρ i)
  let f1 i := honorarium (F i) (t i) μ p U (ρ i)
  let f2 i := burnished (F i) U (ρ i)
  have hl j := campaign (H j).2.1 (h j).1 hu (t j) (H j).1 hη hg hP
  let V := blank C G
  have hf : V.Bounds q w (rowPrice w M) 0 := blank_cap hw hR (hF 1) le_rfl le_rfl
  obtain ⟨D3,D4,hD3,hD4,hE⟩ := I c hm C q z u hR (hF 1) ht f0 (fun i => (hl i).1) (fun j => violet (h j) (H j).2.1 (H j).2.2 hu he (HY j).1 (HY j).2 hf (rows_layout rfl) (hF _) (hx j) _) X hX hh ho
  have hp (j) := low_columns hf (rows_layout rfl) (hF _) (hx j)
  let i' : Ink G 2 := fun _ => i
  have hr := hK i' (fun _ => coord 0)
  have hM : 0 ≤ M := (price_step_metric hw hW (plaquette ⟨(0,1),by decide⟩) (plaquette ⟨(1,2),by decide⟩)).budget_nonneg
  obtain ⟨g,H',hx',Hz⟩ := Q c hm f1 f2 (fun j => inputSeries q V) Φ R M ε α L C.metric i hr.1.budget_nonneg hr.2.1.budget_nonneg hM hε (fun i j => (hW i j).mono (min_le_right ..) le_rfl) (hF 1).starts (fun i => ⟨(hl i).2.1,(hl i).2.2,stain_knit V q hf⟩) (fun i j=> ⟨(hK i j).1.mono hS (min_le_left ..) le_rfl,(hK i j).2.1.mono hS (min_le_left ..) le_rfl,(hK i j).2.2⟩) fun j => ⟨according (C.metric.rights w M hW hw.le) (hp j).2.2,hz j⟩
  let T := emitBase G C g D3 D4
  let Z := (Φ + |alphaPay i α| * bedCharge (min σ w) M+R)*D
  have hΛ (s' A' Λ') (hp : 0<s') (hb : s'≤min a b) (hu : rowPrice w M ≤ A') (hz : X*K≤A') (hv : Z≤Λ') : T.Bounds q s' A' Λ' := by
    have hm : s'≤w := (hb.trans ((min_le_right ..).trans h₂)).trans (min_le_right ..)
    have hg := H'.mono (hb.trans (min_le_right ..)) hv
    exact build_cap C hp (fun i j => (hR i j).mono hm le_rfl) (hF 1) (le_trans (show rowPrice s' M ≤ rowPrice w M by unfold rowPrice; gcongr) hu) hg.1 (hD3.mono (hb.trans (min_le_left ..)) hz).1 (hD4.mono (hb.trans (min_le_left ..)) hz).1 (fun i => ⟨hg.2 _, hD3.2 _,hD4.2 _⟩) (fun i x => hx' i x T rfl)
  have hT := hΛ (min a b) (max (rowPrice w M) (X*K)) Z (lt_min ha hb) le_rfl (le_max_left ..) (le_max_right ..) le_rfl
  exact ⟨T,rfl,rows_layout rfl,hΛ,fun j => achieved (h j).1 (H j).2.1 hu hT _ (H j).1 hη (hE g j),fun j Θ W Ω hg' => draft_pipe (t j) (H j).2.1 (h j).1 hu hT (H j).1 hη hg hP (hv j) (Hz j) _ _ _ hg'⟩
end all
end YM.Stationary
end
