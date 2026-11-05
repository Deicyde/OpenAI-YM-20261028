import YM.RemainderComparison.Cadence.Consonance
/-!
 # Full order two parity proof. integral only after sym adding; no integrability
 conjectures on untruncated V≠0 law. Marks not put into this argument.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Cadence.Glade
open Matrix Filter Function Metric Set ProbabilityTheory MeasureTheory Finset
open Lattice RG Push.AbsoluteSums ConnectedActivityE6 Trace Germ
open Coat PhysicalNext.Repeat Lantern Poll Blaze Brush Shield Flux Progress.StationaryScenes Green
open scoped Topology BigOperators Classical NNReal ENNReal ContDiff
variable {G : Gauge} {L : Side} {p q : ℝ → ℝ}
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {n j : ℕ} {v u D d x e c C A B : ℝ} {Q : E → Matrix ι ι ℝ} {ρ : E→Body ι} {ϕ ψ:E×Body ι→ℝ}
local notation "ℰ" => ℝ×E
local notation "Ξ" => Poll.Body ι
variable (h : Lantern.Golf ϕ ψ ρ Q n D d d C)
local notation "Mt"=> (fun x=>(Q x)⁻¹)
local notation "μ₀" => sweep (Q 0)⁻¹
local notation "g₁"=> Lantern.grace ϕ ψ ρ Q
local notation "Y'"=> fun (x:E) z=> Real.exp (g₁ z (0,x))
local notation "Y"=> (Y')
local notation "Z₁"=> (fun z:Ξ=> Real.exp ∘ (g₁ z))
local notation "Ξ₀"=> Germ.primary ϕ ψ ρ Q

include h
variable (hv:Germ.Contract (Q 0)⁻¹ c)(hc:0<c)
lemma sculpt (hf:0<v)(hu:v≤d): Lantern.Golf ϕ ψ ρ Q n D v v C:=⟨hf,hf,hu.trans h.small,hu.trans h.small,h.off,fun _ hx=> h.curve _ (hx.trans_le hu),
    fun z t x hz ht hV hx=> h.color z t x hz ht (hV.trans_le hu) (hx.trans_le hu), fun x hx z=> h.station x (hx.trans_le hu) z,fun x hx=> h.gram x (hx.trans_le hu) ⟩
variable [FiniteDimensional ℝ E]
include hv hc
variable (hi : 1≤ n)
omit hc hv
include hi
omit h hi
lemma exponent (j:ℕ): ∃ C:ℝ, 0<C∧ ∀ i∈Set.Icc (-1:ℝ) 1, Brush j C 1 Real.exp i:= Brush.compact isCompact_Icc (fun _ _=> Real.contDiff_exp.contDiffAt)
def exAllowance (j:ℕ):=Classical.choose (exponent j)
include h hi
lemma earnings (U₀ :ℝ) (he0:0<U₀) : ∃ v:ℝ, (0<v)∧ Germ.Cloud (Ξ₀) D v U₀ n ((n+2)*n) (Lantern.clump n (Germ.canopy n D U₀ C+Germ.canopy n 1 U₀ (C+1)) (exAllowance n)):=by
   let A:= Lantern.fee n C D; let M:=1+|A|; let d':=min d M⁻¹; have hu :0<M:= by unfold M; positivity
   have ht:0<d':= lt_min h.pos (inv_pos.mpr hu)
   obtain ⟨v,hv,h',he⟩:= tiny_apron ht he0
   have hp: A*d'≤1:= le_trans (mul_le_mul_of_nonneg_right ((le_abs_self _).trans (le_add_of_nonneg_left zero_le_one)) ht.le) ((mul_le_mul_of_nonneg_left (min_le_right ..) hu.le).trans_eq (mul_inv_cancel₀ hu.ne'))
   have hx:= sculpt h ht (min_le_left ..)
   have hM:=Classical.choose_spec (exponent n)
   refine ⟨v,hv, (far_closure hx h' he he0).exponents ?_ hM.2 ?_⟩
   · intro i hy z hz; obtain ⟨hz',hζ⟩:= (patch_test ..).1 (kite_moves h' he hy); exact abs_le.mpr (ether _ hx hζ hz' hi (by rw [max_self]; exact hp) _ hz)
   intro i h z; unfold coloring; rw [kite, zero_smul,Lantern.zeroC,abs_zero]; norm_num
local notation "q₁"=> fun k:ℕ=>fun x:E=>fun z=> Trace.coefficient (fun x=> Ξ₀ x z) k x
local notation "qt"=> q₁
local notation "Lw"=> fun k:ℕ=>fun z:Ξ=> iteratedFDeriv ℝ k (Z₁ z) 0
omit hi
lemma fruits (z:Ξ) : ContDiffAt ℝ n (Z₁ z) 0 := by -- wrong arbitrary A. make smooth only.
    obtain ⟨v,hv,hP⟩:= Germ.larger h (norm_nonneg z)
    exact ((Lantern.compel _ hP (x:=((0:ℝ),(0:E))) (norm_zero.trans_lt hv) (norm_zero.trans_lt hv) le_rfl).smooth).exp
include hv hi
lemma generous (x:E)(i:ℕ)(h₁:i≤n): Integrable (qt i x) μ₀:=by
   obtain ⟨v,-,hY⟩:= earnings h hi (‖x‖+1) (by positivity)
   exact (Germ.budget (Q 0)⁻¹ hY (h.gram 0 (norm_zero.trans_lt h.pos)).1.inv.posSemidef hv le_rfl x (lt_add_one _) (k:=i) h₁ Set.univ).1 -- le_rfl specify
omit hv hi
lemma life (x:E)(i:ℕ)(h₁:i≤n)(z:Ξ) : qt i x z = (i.factorial:ℝ)⁻¹ • Lw i z (fun _=> (1,x)):=by
   let Yz:=Z₁; let F':ℰ→ℝ:=fun y=> Ξ₀ y z; let L:= (ContinuousLinearMap.id ℝ ℝ).smulRight ((1:ℝ),x)
   have ht : kite (0,x)=0:=by simp [kite] -- simp closes?
   have hy : ContDiffAt ℝ i (Yz z) 0:=(fruits h z).of_le (Nat.cast_le.mpr h₁)
   have hf : ContDiffAt ℝ i F' (0,x):= (ht.symm ▸ hy).comp (f:=kite) _ (contDiffAt_fst.prodMk (contDiffAt_fst.smul contDiffAt_snd))
   change Trace.coefficient F' i x= _; rw [ringing _ _ hf]; rw [show (fun t:ℝ=>F' (t,x))=Yz z ∘ L from funext fun t=> congr_arg (Yz z) (show kite (t,x)=L t from by simp [kite,L])]
   rw [linear_pull L (by rw [map_zero]; exact hy),map_zero,ContinuousMultilinearMap.compContinuousLinearMap_apply]; simp only [L,ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.id_apply,one_smul]; rfl

abbrev negRay (E : Type*) [NormedAddCommGroup E][NormedSpace ℝ E]: (ℝ×E)→L[ℝ](ℝ×E):= ContinuousLinearMap.prod (-ContinuousLinearMap.fst ℝ ℝ E) (ContinuousLinearMap.snd ℝ ℝ E)
lemma vibrating (x:E)(i:ℕ)(h₁:i≤ n)(z:Ξ) : qt i x (-z) = (i.factorial:ℝ)⁻¹ • Lw i z (fun _=>(-1,x)):=by
   rw [life h x i h₁]; have hy : Z₁ (-z)=(Z₁ z) ∘ negRay E:= funext fun i=> congr_arg Real.exp (show g₁ (-z) i= _ from by
       let G:=negRay E; convert Lantern.oppositeC ϕ ψ ρ Q (G i) z using 2; simp [G,negRay]) -- edit
   change _ • iteratedFDeriv ℝ i (Z₁ (-z)) 0 _ = _; rw [hy,linear_pull (negRay E) (by rw [map_zero]; exact (fruits h z).of_le (Nat.cast_le.mpr h₁)),map_zero,ContinuousMultilinearMap.compContinuousLinearMap_apply]; rfl
local notation "Hw"=> fun i:ℕ=>fun (x:E) (z:Ξ)=> iteratedFDeriv ℝ i (fun y=>Y y z) 0 (fun _=>x)
lemma helicity (x:E)(i:ℕ)(h₁:i≤n)(z:Ξ) : Hw i x z=Lw i z (fun _=>(0,x)):=by
   let L:=ContinuousLinearMap.inr ℝ ℝ E
   change iteratedFDeriv ℝ i ((Z₁ z) ∘ L) 0 _ = _; rw [linear_pull L (by rw [map_zero]; exact (fruits h z).of_le (Nat.cast_le.mpr h₁)),map_zero,ContinuousMultilinearMap.compContinuousLinearMap_apply]; rfl
lemma sync (x:E) (z:Ξ) (h₁:2≤ n) : qt 1 x z+ qt 1 x (-z)=2*Hw 1 x z ∧ qt 2 x z+qt 2 x (-z)=2*qt 2 0 z+Hw 2 x z:=by
    rw [vibrating h _ _ (by omega),vibrating h _ _ (by omega),helicity h _ _ (by omega),helicity h _ _ (by omega),life h x _ (by omega),life h _ _ (by omega),life h _ _ (by omega)] -- β reduce before?
    let F:=Z₁ z; let a:=fderiv ℝ F 0; let b:=fderiv ℝ (fderiv ℝ F) 0; let h:ℰ:= (1,0); let v:ℰ:= (0,x)
    have hv:h+v=(1,x):=by simp [h,v]
    have hh : -h+v=(-1,x):=by simp [h,v]
    dsimp only []; simp only [show Nat.factorial 2=2 from rfl,Nat.factorial_one,Nat.cast_one,inv_one,one_mul,Nat.cast_ofNat, smul_eq_mul,iteratedFDeriv_one_apply,iteratedFDeriv_two_apply]
    change a (1,x)+ a (-1,x)= 2*a v∧ (2:ℝ)⁻¹*b (1,x) (1,x)+(2:ℝ)⁻¹*b (-1,x) (-1,x)= 2*((2:ℝ)⁻¹*b h h)+b v v
    rw [←hv,← hh, map_add,map_add,map_add,map_add,map_neg]; simp only [_root_.add_apply,_root_.neg_apply, map_add,map_neg]; constructor <;> ring
include hv hc
lemma earned (h₁:2≤n)(x:E) : warrant ((Q 0)⁻¹) (Ξ₀) 1 x=0 ∧ warrant ((Q 0)⁻¹) (Ξ₀) 2 x=warrant ((Q 0)⁻¹) (Ξ₀) 2 0:=by
    have hZ:= sheltered h hv hc 1 (by omega) (by omega) x; have hZ':=sheltered h hv hc 2 (by omega) h₁ x; let μ:=sweep (Q 0)⁻¹
    let p:=qt; let f:=p 1 x; let g:=p 2 x; let k:=p 2 0; let W:= Hw 1 x; let V:=Hw 2 x; let F' z:= f (-z); let G' z:= g (-z)
    have hf : Integrable f μ:= generous h hv (by omega) x 1 (by omega); have hg : Integrable g μ:= generous h hv (by omega) x 2 h₁; have hk : Integrable k μ:= generous h hv (by omega) 0 2 h₁
    have hp : ∀ f:Ξ→ℝ,(∫ z,f (-z) ∂μ)=∫ z,f z ∂μ:= by
       intro u; have hy:=(h.gram 0 (norm_zero.trans_lt h.pos)).1.inv; unfold μ; rw [Shield.recommends _ hy, Shield.recommends _ hy]; rw [← integral_neg_eq_self (fun z:Ξ=> lens₀ ((Q 0)⁻¹) z*u z)]; simp_rw [Lantern.symL]
    have hS:F'=(2:ℝ) • W-f:= funext fun z=> by change f _= _; change f _ = (2:ℝ)* (W z) -f z; change F' z= _; have he : f z+F' z=_:= (sync h x z h₁).1; change _=2*W z at he; linarith only [he]
    have hT:G'=(2:ℝ) • k+V -g:= funext fun z=> by change g _= _; change G' z=(2:ℝ)* k z+V z-g z; have he : g z+G' z=_:= (sync h x z h₁).2; change _= 2*k z+V z at he; linarith only [he]
    have hf' : Integrable F' μ:= by rw [hS]; exact (hZ.1.smul _).sub hf -- .smul args
    have hg' : Integrable G' μ:= by rw [hT]; exact ((hk.smul _).add hZ'.1).sub hg
    have he : (∫ z,f z ∂μ)+(∫ z,F' z ∂μ)=0:=by rw [← integral_add hf hf',show (fun z=>f z+F' z)=(fun z=> (2:ℝ) * W z) from funext fun z=> (sync h x z h₁).1,integral_const_mul,hZ.2,mul_zero] -- leq
    have hu:= hp f; change (∫ z,F' z ∂μ)=_ at hu; rw [hu] at he
    change (∫ z,f z ∂μ)=0∧ (∫ z,g z ∂μ)= ∫ z,k z ∂μ; refine ⟨by linarith only [he],?_⟩
    have H : (∫ z,g z ∂μ)+(∫ z,G' z ∂μ)=2*∫ z,k z ∂μ:=by rw [← integral_add hg hg',show (fun z=>g z+G' z)=(fun z : Ξ=> 2*k z+V z) from funext fun z=> (sync h x z h₁).2, integral_add (hk.const_mul _) hZ'.1,integral_const_mul,hZ'.2,add_zero]
    have hv:= hp g; change (∫ z,G' z ∂μ)=_ at hv; rw [hv] at H; linarith only [H]
end YM.RemainderComparison.Cadence.Glade
