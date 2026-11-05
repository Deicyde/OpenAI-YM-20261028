import YM.UVExtension.Wick.Cobalt

set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Wick
open Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid
open ConnectedActivityE6 Blaze Shell Channel SliceRows Control Window Census Green Mask Pulse Itinerary Coat Footprint Raw Poll Pond
open Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill
open Packets Art Silica Shield Eider Flux Hues Rotation Matter
open Lamppost MeasureTheory Set Filter
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff ENNReal InnerProductSpace Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G} {Z : ChartRatio G}
variable (X : Coat T F) {R : RG.Rep G f} {u v s a : ℝ} {z : Air f G} {Y : Config G c}
open Animals Reserves
variable {ι : Type} [Fintype ι]
variable {x y γ W μ δ e b B C u D d r q' A v' g w b' Y' n:ℝ} {K l j : ℕ} {χ:Chi} {Q : YM.ConnectedActivityE6.Target G P}
    {o : Target.Order G W} {H : Cash W x μ L Q o a T R} {V : ι→ Juice G f}
namespace Bower
variable (N : Bower Q o L S.patch μ χ A b x j K u B C r d n) (hS:Stamp T) (hF : Festa Q L H V w g)

variable {X} (hX:X.x=x)(hm:X.manifest)(hc:X.χ=χ)(hr:X.width=o.K)
variable (z : Vines ι) (hv:z∈parade (ι:=ι) (betaF G x L) g)
set_option quotPrecheck false
variable (hq : ‖z none‖/ (z none).re≤2)
variable {H' : Cash W x μ L Q o a T (flight R (z none).re)}
-- simultaneous angular certificates.
structure Lush (N : Bower Q o L S.patch μ χ A b x j K u B C r d n) (hF:Festa Q L H V w g) (z:Vines ι) (hp:z∈parade (betaF G x L) g)
    (ξ : ℝ) (J' : Mixed.Costs) where
    link : Cash W x μ L Q o a T (flight R (z none).re)
    conduit : Utopia link j u d r C χ
    peeled : Alphabet c f → ℝ
    toll : Alphabet c f → ℝ
    nonneg : ∀ i,0≤ peeled i
    acct : Mixed.Accounts S Q.halo (radiusB x) J' H.birth toll (lengths T R) (steamP S J')
    pair : J'.Buy L Q.halo (radiusB x)
    tabs_m (i:Molecule S) : (∏ k∈i, tabs S J' (radiusB x) Q.halo peeled k)*conduit.rad^(blaze i).card=∏ k∈i,tabs S J' (radiusB x) Q.halo toll k
    breathes : ∀ (D:Type) [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D] (V':D→Config G c)
      (F:Forest S.ratio) (X:Coat T F), X.x=x → X.χ=χ → X.width=o.K → X.manifest → ∀ (z':D) (w:Air f G), Mode V' z' j u →
      V' z'=X.V → (∀ I:Finset (Bond f),Brush j 1 (ξ * facescale I (scaled (z none).re w)^K) (fun t=> scorched X A I (V' t) (z none) w) z') ∧
      ∀ k, ∀ i:Head S, Healthy (temp X.x) (H.supportP i) X.V → Brush j (tabs S J' (radiusB x) Q.halo peeled i) (r*spanW T R (radiusB x) Q.halo i) (fun v=>
        amberP (vary X (V' v)) R Q.table W o.a k Q.halo V (z none) (z ∘ some) (sailplane X A w (V' v)) (steer X A (loom X w) (V' v)) (X.input (loom X w)) i) z'

section ports
variable (Ξ:Utopia H' j u d r C χ) {f' : ∀ i:ι,Cash W x μ L Q o a T (chunk R (V i) ((z none).re))} (Φ:∀ i,Utopia (f' i) j u d r C χ)
    (L' M' C₀ p q t : ℝ) (hl:Q.rate≤γ) (hg:γ<0)
local notation "Z₀"=> stalk Q hl hg
variable (hP: ((stalk Q hl hg).costs L μ ((z none).re) x (C+p+q)).Buy L Q.halo (radiusB x))
    (hW : Sales (radiusB x) Q.relative Q.ε H.birth (fun i=> t*platK Ξ.flair (fun j=>(Φ j).flair) g i)
      (Sum.elim (forcedExtra R) (Sum.elim (exCharge T R) (fun _=>0))) (betaF G x L^γ))
    (η a' : ℝ)
    (hh : 0≤p) (hy:0≤n) (ht :1≤t) (hpL:0≤L') (he:L'*M'≤t) (hp:L'≤t)
    (h₁ : ∀ (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (x:E) (w d:ℝ) (f:E→ℝ),
      w≤1/2 → Brush j w d (fun i=>Real.exp (f i)-1) x → Brush j (L'*w) d f x)
    (h₂ : ∀ (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (x:E) (w d:ℝ) (f:E→ℂ),
      Brush j w d f x→ w≤1 → Brush j (M'*w) d (fun i=> Complex.exp (f i)-1) x)
    (h₃ : ((betaF G x L)^ Q.rate:ℝ) ≤ 1/2) (h₄ : (betaF G x L)^γ≤1)
    (hζ : ∀ P:Stores S, 1≤P.shares → (1+r+(1+j.factorial*a')*(1+48*n*P.shares))^j ≤ Wick.chimney P q G L x)
    (hA:∀ (F:Forest S.ratio) (X:Coat T F),X.x=x → ∀ (P:Stores S) (q:ℝ), ‖warmth X ((z none).re) (z none) P q‖≤Wick.chimney P p G L x)
    (hY:Brush j a' 1 Complex.exp 0) (hD:Brush j η 1 Real.log 1)
include hv hP hW hζ hA hY hD hh hy ht hpL he hp h₁ h₂ h₃ h₄ hS hq
lemma launching : Nonempty (Lush N hF z hv ((1+(1+j.factorial*a')*(1+24*(j.factorial*η+j.factorial*η))*2)*(B*2^K)) ((stalk Q hl hg).costs L μ ((z none).re) x (C+p+q))) := by
  let v0:=tallyP z Ξ Φ t g; let Q':=tallyQ z Ξ Φ t g; let b':=radiusB x
  have hT:= zero_le_one.trans ht; have hx i:= funnelZ z Ξ Φ t hT ht (le_trans hF.margin.le hF.bound) i
  have hz: Sales b' Q.relative Q.ε H.birth Q' (Sum.elim (forcedExtra R) (Sum.elim (exCharge T R) (fun _=>0))) (betaF G x L ^ γ) := by
    convert hW.shift (A:=1) zero_le_one (fun i=>(hx i).2.1) (fun i=> by rw [one_mul]; exact (hx i).2.2) using 1; simp
  refine ⟨⟨H',Ξ,v0,Q',(fun i=> (hx i).1),⟨fun i _=> ⟨mul_nonneg hP.capture (Real.exp_pos _).le,le_rfl⟩,hz.nonneg,fun _=> Nat.cast_nonneg _,hz.hit⟩,hP,?_,?_⟩⟩
  · intro i; rw [cumulate i,cumulate i]; let A:=i.toRight; let r:=Ξ.rad
    have hu : (∏ i∈A,Q' i)=(∏ i∈A, v0 i)*r^ (blaze i).card:= by
      rw [cumulate A,cumulate A]; let Z:=A.toRight; let f j:=Q' (.inr j); let g' j:=v0 (.inr j)
      change (∏ i∈A.toLeft,Q' (.inl i))* (∏ j∈Z,f j) = ((∏ i∈A.toLeft,Q' (.inl i))* (∏ j∈Z,g' j))*_
      rw [mul_assoc,cumulate Z f,cumulate Z g']; apply congr_arg; rw [mul_assoc]; apply congr_arg _
      change ((∏ _∈ blaze i,Ξ.M*Ξ.rad):ℝ)= (∏ _∈blaze i,Ξ.M)*r^(blaze i).card; rw [prod_mul_distrib]; simp [r]
    rw [mul_assoc]; exact congr_arg (fun x=> _ *x) hu.symm
  intro E _ _ _ V' F X he' hX hW hM τ y hh ht₀
  refine ⟨fun I=> ?_,fun k i hi=> ?_⟩
  · have hx:= scallop N hS hF he' hM hX hW z hv hq ht₀ hh I y η a' hD hY
    exact hx
  let f t:= steer X A (loom X y) (V' t)
  rcases i with i|i
  · by_cases hz: Packets.connected S Q.halo b' i; swap; · apply Brush.zi (Eventually.of_forall (fun p:E=> if_neg (show ¬Packets.connected S Q.halo (vary X (V' p)).B i from (by unfold b' at hz; rwa [show (vary X (V' p)).B=radiusB x from congr_arg _ he'])))); unfold tabs Mixed.costs; rw [Sum.elim_inl,if_neg hz]; · change 0≤r*1; linarith [Ξ.active]
    have hY': X.B=radiusB x:=congr_arg _ he'
    have he := starbud N hS hF he' hM hX hW z hv hq ht₀ hh Ξ hy i (hY'.symm ▸ hz) (hY'.symm ▸ (show Healthy _ (i.dome (Q.halo*b')) X.V from hi)) k y a' hY p (hA _ X he' i _)
    apply he.climb
    · change Wick.chimney _ _ _ _ _ * Ξ.tag _ * _ ≤ _
      have hK0 : 1 ≤ i.shares:= Packets.shares_nonzero S _ _ hz
      apply le_trans (mul_le_mul_of_nonneg_left (hζ i hK0) (mul_nonneg (Real.exp_pos _).le (Ξ.tagged _)))
      unfold Utopia.tag stout tabs Mixed.costs; dsimp only [Sum.elim]; unfold b' at hz; rw [if_pos hz,if_pos hz]
      change Wick.chimney _ _ _ _ _ * steamP S (Q.costs L μ (z none).re x C) _ * _ ≤ steamP S (Q.costs L μ (z none).re x (C+p+q)) i; rw [growfit,mul_comm,growfit q]
    change _ ≤ r * 1; rw [mul_one]; exact Ξ.active
  exact easel N hS hF he' hM hX hW z hv hq ht₀ hh Ξ Φ L' M' t hl hg hT he hpL hp ht hz h₁ h₂ h₃ h₄ y k i hi
end ports
end Bower
end YM.UVExtension.Wick
