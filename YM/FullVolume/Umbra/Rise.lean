import YM.FullVolume.Umbra.Rope
-- one real mark among any two epoch carpets at the same stamp
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Lim
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration PhysicalNext.Repeat Greenbelt Match Song Refrain
open Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open UVNext.CouplingReset Animals Progress.DirectedRecipe Ovens
open Stationary Stationary.Shade Stationary.Beacon Laurent Exterior Bloch
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {P : Teller G} {S : StepData c f} {F : Forest S.ratio}
open Matrix Window Progress.StationaryScenes Green Census Control Flux FullVolume.Shadow
open Gate Frond Vine Mask
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E] {φ: Filter ℕ}{J: Ultrafilter ℕ}{Q:ConnectedActivityE6.Target G P}{W x μ C₀ a b e ℓ v :ℝ}{o:Target.Order G W}
    {Λ: Era G S}{U:ℕ→ E→ Config G c}{Z: Draft F G} {K H:ℕ→ Epoch Λ}{j:ℕ}{p:E}
open FullVolume.Neptune Flux Shield Eider Packets Polar
namespace Umbra
open Lotus
variable {M:Bank}(I:Depot Q o x μ L C₀ K) (T:Depot Q o x μ L C₀ H){χ: Chi}(R:∀ n, Station M χ (I n) j)(P':∀ n,Station M χ (T n) j)
variable {F₀:BatchK K}(hK:Sweep K){k:Lotus.Wing}(hk:Hush F₀ k)
-- no dependence on inspection branch S/Π signs, use integral. keep polynomial moment I for tail compare.
structure Seats (δ:ℕ→ Molecule S→ℝ) (Δ:ℕ) : Prop where
    bud : Sparse δ
    window : ∀ n (X: Forest S.ratio) (V: Coat (K n).tubes X), V.manifest→ V.x=x → V.width=o.K → V.χ=χ →∀ p z,
       ‖(F₀ n).into V W o.a Q.table (own p) Q.halo p z‖ ≤ δ n p
    gaze : ∀ n (X:Forest S.ratio) (V:Coat (K n).tubes X), V.x=x→ V.width=o.K→ V.χ=χ→ V.manifest→∀ i,Healthy (Pressure.temp x) ((I n).unionP i) V.V→∀ (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E](U:E→ Config G c)(p:E), Mode U p j M.v→ U p=V.V→∀ y : X.Slice G×Air f G, ∀ D:Finset (Bond f), Brush j (δ n i * facescale D y.2 ^ Δ) 1 (fun v=> (F₀ n).carat D V (U v) M.A Q.table i W o.a Q.halo y) p
include I R hk hK
set_option maxHeartbeats 520000 in
lemma spout: ∃ (Δ:ℕ)(w:ℕ→ Molecule S→ℝ),Seats I (F₀:=F₀) (χ:=χ) (M:=M) (j:=j) w Δ:=by
   obtain ⟨G',hG⟩:= coined M I R hK; let ζ:= k.badge S; let p n (i:Molecule S):=if ζ∈i then ∏ j∈i.erase ζ,G' n j else 0; let f n i:=cashing G' ζ i j n
   have hp:Sparse p:= erasers hG.silver.arbitrary ζ
   have hf:Sparse f:= erasers (hG.silver.climb (show 0≤(2:ℝ)^j by positivity)).arbitrary ζ
   obtain ⟨b,hb⟩:= hk.bounds; have hb':0≤b:= (F₀ 0).profit.trans (hb 0)
   obtain ⟨v,hv,hV⟩:= boundCone M I R; let b':= b*v*(1+(1+1:ℝ))^j; have hb₀:0≤b':=by unfold b'; positivity
   have hM:0≤M.p:= (R 0).fleets.M.pos; let t:= M.K*j; let c':= (3+M.p)^j; have he:0≤c':=by unfold c'; positivity
   let W' n (i:Molecule S):= b*p n i+c'* (b'*f n i)
   refine ⟨t,W',⟨(hp.climb hb').tug ((hf.climb hb₀).climb he),fun n X V hM hc hv hx i z=>?_,?_⟩⟩
   · exact (canted I R hk (X:=V) i hG hM hc hv hx z.1 z.2).trans ((mul_le_mul_of_nonneg_right (hb n) (hp.value n i)).trans (le_add_of_nonneg_right (mul_nonneg he (mul_nonneg hb₀ (hf.value ..)))))
   intro n F X hx hk' hχ hX i H U _ _ _ V s hv hg y D
   let f₁:=(F₀ n); let Y:= X.wrapY y.1
   let Z(y':U):=(vary Y (V y')).enforce (2*o.a) (steer Y M.A (worldZ Y (K n).beta y.2) (V y')) (Y.plaza (areas (K n).kin (K n).tubes 0 Y.B (f₁.turn.badge S)))
   have h₁ : Brush j v 1 Z s:= hV n F Y hx hk' hχ hX y.2 U V s hg hv (areas (K n).kin (K n).tubes 0 Y.B (f₁.turn.badge S))
   let Ux:= Y.input (worldZ Y (K n).beta y.2); have h₂: Brush j b 1 (fun _=> f₁.ingredient Ux) s:= (Brush.certified zero_le_one _).climb ((f₁.earn _).trans (hb _)) le_rfl -- edit
   have hQ: Brush j b' 1 (fun s'=> f₁.fond (vary Y (V s')) o.a (steer Y M.A (worldZ Y (K n).beta y.2) (V s')) Ux) s:= (h₂.paints h₁).trim
   let d:= facescale D y.2
   refine (histories I R hk i (X:=Y) hx hχ hk' hX hv hg y.2 D hG H hQ).climb ?_ le_rfl
   have h': 1 ≤ d:= (Flux.expenses ..).1; have hz: 1 ≤ d^M.K:= one_le_pow₀ h'; let u:= f n i
   have hf: 0≤u:= hf.value ..
   change 1*(b'*u)*(1+(M.p*d^M.K+1+1))^j ≤ W' n i*d^t -- parentheses
   calc
     _ ≤ 1*(b'*u)*((3+M.p)*d^M.K)^j:=mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith only [hz]) _) (by positivity)
     _ = c'*(b'*u)* d^t :=by unfold c' t; rw [mul_pow,pow_mul]; ring
     _ ≤ _:=mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (mul_nonneg hb' (hp.value ..))) (by positivity)
namespace Seats
variable [FiniteDimensional ℝ E] {δ:ℕ→Molecule S→ℝ}{Δ:ℕ} {i:Molecule S}
  (h:Seats I (F₀:=F₀) (χ:=χ) (M:=M) (j:=j) δ Δ)
include I R h
omit hK hk
lemma closeH (m:ℕ)(X:Coat (K m).tubes F)(hx:X.x=x)(hv:X.width=o.K)(hψ:X.χ=χ)(hm:X.manifest)(i:Molecule S) : |(F₀ m).tithe X (own i) W o.a Q.table Q.halo i| ≤ δ m i:=by
     have H':Cash W X.x μ L Q o C₀ (K m).tubes (K m).kin:=hx.symm ▸ (I m); have he:=(F₀ m).tip X (own i) H' hv hm i
     exact (norm_integral_le_integral_norm _).trans ((integral_mono he.2.1.norm (integrable_const _) (h.window m F X hm hx hv hψ i)).trans_eq (by simp))
lemma journal (m:ℕ)(X:Coat (K m).tubes F)(hx:X.x=x)(hv:X.width=o.K)(hψ:X.χ=χ)(hm:X.manifest) (V:E→ Config G c)(p:E)(ht:Mode V p j M.v)(hg: V p=X.V):
     let D:=edgesM S ((I m).unionP i) (radiusB x)
     let f s:= (F₀ m).carat D X (V s) M.A Q.table i W o.a Q.halo
     let v:= (F.order G).prod X.dice
     Blaze.Meristem f p v j ∧ ((fun s=> (F₀ m).cinema (vary X (V s)) i W o.a Q.table Q.halo (podium S G ((I m).unionP i) (radiusB x))) =ᶠ[𝓝 p] fun s=> ∫ z,f s z ∂v):=by
    intro D f₁ Ln;  have H':Cash W X.x μ L Q o C₀ (K m).tubes (K m).kin:=hx.symm ▸ (I m) -- L name
    let R':= (R m).N.oboe; have he:= R'.flow _ X hx hψ hv hm E V p hg ht
    have hN: 8*o.a*Pressure.fiery G X.x S.patch.L≤ M.A/2:=by rw [hx,(I m|>.laws.data.funds.length_eq)]; exact R'.mode
    have hL:= Leaf.chutes (F₀ m) X i H' hv hm he R'.conduit (show 8*o.a*Pressure.fiery G X.x S.patch.L≤ M.A/2 from hN)
    have hb : podium S G (H'.unionP i) X.B= podium S G ((I m).unionP i) (radiusB x):=by change podium S G (ground _ (K m).tubes Q.halo (radiusB X.x) i) (radiusB X.x)=_; rw [hx]; rfl
    refine ⟨((F₀ m).boosts X i H' hv hm D he R'.conduit (by assumption)|>.1),?_⟩
    have hh : edgesM S (H'.unionP i) X.B=D:=by change edgesM S (ground _ (K m).tubes Q.halo (radiusB X.x) i) (radiusB X.x)=_; rw [hx]; rfl
    rw [hb,hh] at hL; exact hL
lemma opal : ∃ q:ℕ→Molecule S→ℝ, Sparse q∧∀ n (F:Forest S.ratio) (X:Coat (K n).tubes F),X.x=x → X.width=o.K→ X.χ=χ→ X.manifest→∀ i,Healthy (Pressure.temp x) ((I n).unionP i) X.V →∀ (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E](V:E→ Config G c)(p:E), Mode V p j M.v → V p=X.V → Brush j (q n i) 1 (fun s=> (F₀ n).cinema (vary X (V s)) i W o.a Q.table Q.halo (podium S G ((I n).unionP i) (radiusB x))) p:=by
   let v(I:Finset (Bond f)):= (lensS I G).card; let B:=payE o.eta o.gap o.ample (tubularPrice G L); let C (I:Finset (Bond f)):= (1+(I.card:ℝ)+v I+v I)^Δ*(1+(v I:ℝ)*(2*Real.exp (B*(Δ:ℝ)^2/2)))
   obtain ⟨b,hb⟩:= (Set.finite_range C).bddAbove
   refine ⟨_,h.bud.climb (abs_nonneg b),fun n F X hx hv hZ hm i hz E _ _ _ V p ht hg=>?_⟩
   let D:= edgesM S ((I n).unionP i) (radiusB x); let v(z:Air f G):= facescale D z^Δ; have he:= ((I n).laws.data.localP _ X hx hv hm).sails; obtain ⟨hL,hq⟩:=globes D he Δ; let u (x:F.Slice G×Air f G):= δ n i*v x.2; let ν:= (F.order G).prod X.dice
   obtain ⟨hp,hV⟩:= h.journal I R (i:=i) n X hx hv hZ hm V p ht hg
   have hK:Integrable u ν:= (hL.const_mul (δ n i)).comp_snd _
   refine Brush.shimmy (?_ : Brush j (|b| *δ n i) 1 _ p) hV; apply hp.buds u hK zero_le_one _ (ae_of_all _ (fun y=> h.gaze n F X hx hv hZ hm i hz E V p ht hg y D))
   rw [integral_prod _ hK]; simp only [u, v,integral_const_mul, integral_const,MeasureTheory.probReal_univ,one_smul]; exact (mul_le_mul_of_nonneg_left (hq.trans ((hb (Set.mem_range_self (f:=C) D)).trans (le_abs_self _))) (h.bud.value ..)).trans_eq (mul_comm ..)
end Seats
end Umbra
end YM.ConnectedActivityE6.Lim
