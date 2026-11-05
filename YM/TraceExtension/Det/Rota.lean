import YM.TraceExtension.Det.Shoal
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Det
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Bloch Exterior Tree RG Wilson Finset Push.Uniform
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{f:Side}{p:Clip}{M:PathData G}{k m n r:ℕ}{α σ μ a b c τ A C D:ℝ}
    (s:Site f)(U:Config G f)
lemma mark_signed (g:Signed) (u:ℝ)(h:M.Bounds p σ A D): marke p M u (pull g 0 U)=marke p M u U:=by
    let V:=pull g 0 U
    have ht : burn p M V ∘ spiral g U=burn p M U:=by unfold V; funext x; rw [Function.comp_apply,burn,← Stationary.wheel]; exact orbit_axis (fun b=>quadratic p M b+ uncut M.cubic b+uncut M.quartic b) _ _
    have he:= brigade (G:=G) (n:=f) g
    have hp:= bridle g U
    have hr: damage (pocket _) (burn p M V ∘ spiral g U) 0=(regimentU g U)ᵀ * flare p M V* regimentU g U:=damage_rate _ _ _ _ (burn_cov V h)
    have hh:= hp.pulls (A:=flare p M V) (B:=flare p M U) (by rw [←hr,ht]; rfl)
    obtain ⟨hz,hw⟩:=shell_mat U u _ _ V hp he (swirl g U) hh
    unfold marke; unfold V at hz hw; rw [hp.turn_det (hp.back hz),he.turn_det (he.back hw)]

variable (G k) in
def rode : (Lines G f k → ℝ) →L[ℝ] (Lines G f k → ℝ):= ContinuousLinearMap.pi fun i=>ContinuousLinearMap.proj (rideI s i)
variable (G k) in
abbrev car:= billsM (pocket _) (pocket _) (rode G k s)
lemma rodex : rode G 1 s=rideC s:=rfl
lemma rox (g:Gauge)(k:ℕ)(x:Lines g f k→ℝ)(i): rode g k s x i=x (rideI s i):=rfl
lemma coxMove (x:BaseSites G f)(i): gaugeColor (rode G 0 s x) i=gaugeColor x (i+s):=rfl
lemma ride_mul {V U:Config G f}: ride s U*ride s V=ride s (U*V):=rfl
lemma mil_c (G:Gauge)(k:ℕ): Military (car G k s):=military_intro _ (fun i j=>by rw [bill_pay,bill_pay]; exact (rideI s).sum_comp (fun z=> i z * j z))
lemma mail_ro : mail (ride s U)*car G 0 s=car G 1 s*mail U:=by
    apply testers; intro x y; rw [← mulVec_mulVec,← mulVec_mulVec,mailed,bill_pay,bill_pay,mailed]; apply congr_arg; apply edgeColor.injective; ext1 ⟨z,j⟩; rw [cant_at,coxMove,coxMove,rodex, spin_at,cant_at]; simp only[add_right_comm];rfl
lemma beam_ro {T:Peat G f}(h: ContDiffAt ℝ ω (bal (ride s U) T) 0): beamH (rj s T) U=(car G 1 s)ᵀ*beamH T (ride s U) *car G 1 s:=by
    let W:=bal (ride s U) T
    let p:=rode G 1 s
    have ht:bal U (rj s T)=W ∘ p:= funext fun i=>by change T (ride s (input _ _ i*U))=T (input _ _ (rideC s i)*ride s U); rw [r_imp,ride_mul]
    unfold beamH; rw [ht]; exact damage_rate _ _ _ p h
lemma mark_c {p:Clip}(u:ℝ)(h:M.Bounds p α C D):
    stock p M u (ride s U)*car G 1 s=car G 1 s*stock p M u U ∧ ammo u (ride s U)*car G 0 s=car G 0 s*ammo u U:=by
    apply shell_mat U _ _ _ _ (mil_c ..) (mil_c ..) (mail_ro s U)
    apply (mil_c s G 1).pulls
    have hp:= beam_ro s U (T:=fun U=>mainTerm p M U) (burn_cov (ride s U) h); rw [show rj s (G:=G) (fun U=>mainTerm p M U)=(fun U=>mainTerm p M U) from funext (fun U=> main_ride s _ _ U)] at hp; exact hp.symm
lemma marks_trans (u:ℝ)(h:M.Bounds p α C D): marke p M u (ride s U)=marke p M u U:=by
    unfold marke; let L:= mil_c s G; rw[(mil_c ..).turn_det ((mil_c ..).back (mark_c s U u h).1),(mil_c ..).turn_det ((mil_c ..).back (mark_c s U u h).2)]
-- works when det is zero too via carried Military: old lemma only invertible
lemma shell_b_c (h:M.Bounds p α C D)(he:(stock p M μ U).det≠0): shellB p M μ (ride s U)*car G 1 s=car G 1 s*shellB p M μ U:=by
    have hx:=(mark_c s U μ h).1; have ht:=mil_c s G 1; exact Military.inverse_cross ((ht.turn_det (ht.back hx)).symm ▸ he.isUnit) he.isUnit hx
lemma shell_g_c (h:M.Bounds p α C D)(hu:0<μ): shellG μ (ride s U)*car G 0 s=car G 0 s*shellG μ U:= Military.inverse_cross (ammo_safe _ hu).det_pos.ne'.isUnit (ammo_safe _ hu).det_pos.ne'.isUnit (mark_c s U μ h |>.2)
lemma bill_cyclic {I:Type}[Fintype I][DecidableEq I]{L:Funds I}(h:Military L)(A:Funds I): (Lᵀ*A*L).trace=A.trace:=by rw[trace_mul_comm _ L,← Matrix.mul_assoc,h.left, Matrix.one_mul]
lemma bill_shane {I:Type}[Fintype I][DecidableEq I]{L:Funds I}{B C H D: Funds I}(h:Military L)(hc:B*L=L*C)(he:H*L=L*D): (B*H).trace=(C*D).trace:= (bill_cyclic h _).symm.trans (by rw [h.back (show B*H*L=L*(C*D) by rw[mul_assoc,he,← mul_assoc,hc,mul_assoc])])
lemma shell_get_s {F:Peat G f}(hc:(stock p M μ U).det≠0)(h:ContDiffAt ℝ ω (bal (ride s U) F) 0)(hp:M.Bounds p α C D):
    (shellB p M μ U*beamH (rj s F) U).trace=(shellB p M μ (ride s U)*beamH F (ride s U)).trace:=by
    have hx:=mil_c s G 1; exact (bill_shane hx (shell_b_c s U hp hc) (hx.pulls (beam_ro s U h).symm)).symm
-- trace basis diagonal root picks orientation. PairT at unshifted
variable {I:Type}[Fintype I]
def diveC (i:Lines G f k): Funds (Lines G f k):= of fun j n=> if j=i ∧ i=n then 1 else 0
-- pointwise row matrix general reindex
lemma car_elem (F:Funds (Lines G f k)) (Z:Funds (Lines G f k)): F*car G k s=car G k s*Z ↔ ∀ i j,F i j=Z (rideI s i) (rideI s j):=by
    constructor
    · intro h i j; let p:=car G k s; let L:Lines G f k→ℝ:=Pi.single (rideI s j) 1
      have hx:p *ᵥ L=Pi.single j 1:=by rw [show p *ᵥ L=_ from bill_pay ..]; funext i; rw[rox]; simp [L,Pi.single_apply];
      have he:=congr_arg (fun q:Funds (Lines G f k)=> (q *ᵥ L) i) h; simp only [← mulVec_mulVec] at he
      change (F*ᵥ(p *ᵥ L)) i=(p *ᵥ (Z*ᵥ L)) i at he
      rw[hx, mulVec_single_one, show p *ᵥ _=_ from bill_pay (rode G k s) (Z *ᵥ L), rox] at he
      simp only [L,Matrix.mulVec_single_one] at he; exact he
    intro h; apply testers; intro x y; rw[← mulVec_mulVec,← mulVec_mulVec,bill_pay,bill_pay]; apply congr_arg; funext i; rw [rox]; simp only [Matrix.mulVec,dotProduct,h,rox]; exact Equiv.sum_comp (rideI s) (fun x=> Z (rideI s i) x * y x)
end YM.Trace.Det
