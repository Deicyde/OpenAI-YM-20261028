import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Peak.Puff
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Peak
open Function Filter Set Lattice Wilson Pressure Precision RG Tree Next Next.SectorChange Next.Fluctuations WardBin.Lies
    Matrix Multi Multi.Vacuum.Jets Multi.Puff ProofPorts.CommonComplexProduction ProofPorts.CommonComplexProduction.Score
    Push.SectorMeasure SelectedOrderedKernels SelectedOrderedKernels.Sector Next.SectorChange.Rows Wisps
    Exterior Planned.AtomRegular MeasureTheory AnalyticBridge.LocalGaussianLaws
open JointLoad JointLoad.Heir
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {A : Stores S} {X : Support f} {Y : Support c}
    {V : Config G c} {P B : BudgetPoint} {ι : Type} [Fintype ι] [DecidableEq ι] {x u t τ : ℝ} {n r m : ℕ} {o : Site f}
    {q : Chi} {d : ℝ} {k : S.Choices} {f' : Config G f → ℝ} {Pt : Teller G} {C : Libretto G n} {D : Record}
variable {Γ : Prices G ι → ℝ} (k q d) (a : Museum F x A X Y ι) (U : Config G f)
variable (he : Plays C D P B Pt T x) (hf : B.Regular X f') (hp:o∈X)
    (hY : Walled S X Y x r) (hu : 0≤u) (hΓ : Silences G ι n u (D.ε*B.threshold) Γ) (hV : Healthy P.threshold Y V)
include he hf hp hY hu hΓ hV
open AnalyticBridge.LocalGaussian.Moments Push.AbsoluteSums Lute
omit he hf hp hY hu hΓ hV in
private lemma thickness (n : ℕ) {a b s : ℝ} (ha : 1 ≤ a) (hb : 0 ≤ b) : (a+b*s^2)^(n+n) ≤ (a+a)^(n+n)*(1+b^(n+n)*s^(2*(n+n))) := by
  let d := n+n
  have hpa : 0≤b*s^2 := mul_nonneg hb (sq_nonneg _)
  rw [pow_mul, ← mul_pow]; rcases le_or_gt (b*s^2) 1 with h|h
  · exact (pow_le_pow_left₀ (by positivity) (add_le_add_right (h.trans ha) a) d).trans (le_mul_of_one_le_right (by positivity) (le_add_of_nonneg_right (pow_nonneg hpa _)))
  rw [mul_add,mul_one,← mul_pow]; apply le_add_of_nonneg_left' (pow_le_pow_left₀ (by positivity) _ _) (by positivity : 0 ≤ (a+a)^d)
  rw [add_mul]; exact add_le_add (le_mul_of_one_le_right (by positivity) h.le) (le_mul_of_one_le_left hpa ha)
where le_add_of_nonneg_left' {u v w : ℝ} (h : u≤v) (he : 0≤w) : u≤w+v := h.trans (le_add_of_nonneg_left he)
variable (hτ : B.supBounds o X f' τ)
include hτ
private lemma coarseWave (hs: ¬ Short S B X) (l:List (Directions G c))(hl:l.length≤ n)(hb:∀ A∈l, P.dirBound (S.ratio.parent o) A)(z:Prices G ι):
    let ρ := Lute.rust C D P B S.patch.L X r x u
    ‖leftDerivs (a.concert T u q d k f' Γ U V z) l V‖ ≤ (beat C*τ)*(1+ρ^(n+n)*powers z^(2*(n+n))):=by
   intro ρ; have ht:=hτ.1
   let t:= (leading C+ρ*powers z^2); let f₁:=Plays.price C D P B S.patch.L X x u z
   have ha: Plays.price C D P B S.patch.L X x u z=grandFee C.rights * (ample n X P B D.Q C.M C.C x)^n:= if_neg hs
   have hq: 0 ≤ f₁:=by
      unfold f₁; rw [ha]; have ht:=ample_one n X P B D.majorant C.matins C.C_one (x:=x); unfold grandFee; have hQ:=patterns_nonneg n; have hb:=C.rights.large; positivity
   have HH := Peak.allotted q d k a U he hf hp hY hu hΓ hV z (f₁*τ) (mul_nonneg hq ht) (fun hx i hi l h=> (Peak.wind (q:=q) (d:=d) (k:=k) he a hf hp hτ hu hV U z (hΓ.stay z hx) hi h).2 _ hi |>.trans_eq (by rw [← ha]))
   let p:= phrase C
   have hw:0≤ρ:= Lute.rust_nn hu; have hc:=leading_one C; have hh : 1 ≤ t := hc.trans (le_add_of_nonneg_right (mul_nonneg hw (sq_nonneg _))); have hD: Lute.decay B S.patch.L X =1:=if_neg hs; have hz:p≥0:=phrase_nn _
   have hg:= pay_le (C:=C) (D:=D) (P:=P) (B:=B) (L:=S.patch.L) (X:=X) (x:=x) (r:=r) hu z; rw [hD,mul_one] at hg
   calc
     _ ≤ (f₁*τ)*t^n:= (HH.caps _ hl hb).trans (mul_le_mul_of_nonneg_left ((pow_le_pow_left₀ HH.sane (speed_le a hY hp hu z) _).trans (pow_le_pow_right₀ hh hl)) (mul_nonneg hq ht))
     _ ≤ (p*t^n*τ)*t^n:=by gcongr
     _ = p*τ*t^(n+n):=by rw [pow_add]; ring
     _ ≤ p*τ*((leading C+leading C)^(n+n)*(1+ρ^(n+n)*powers z^(2*(n+n)))):=mul_le_mul_of_nonneg_left (thickness n hc hw) (by positivity)
     _ = _ :=by unfold p beat; ring

-- integrated meter. No movement outside hymn representation only at CORNER hV. Enough for later Debt.Effect
omit he hf hp hY hu hΓ hV hτ in
private lemma meter_mono {Q : ℝ} (hq:0≤Q){D H:ℕ}(k:ℕ)(h:D≤H): AnalyticBridge.LocalGaussian.Moments.meter D 0 Q k≤AnalyticBridge.LocalGaussian.Moments.meter H 0 Q k:=by
   have h:= inflate_ge k (show 0≤Q⁻¹/8 by positivity); unfold AnalyticBridge.LocalGaussian.Moments.meter; gcongr
omit hτ
lemma frozen (z:ℝ)(l:List (Directions G c))(hl:l.length≤n)
    (t:ℝ)(ht:0≤t)(hz:0≤z)(hh:∀ x: Prices G ι, ‖leftDerivs (a.concert T u q d k f' Γ U V x) l V‖ ≤ z*(1+t^(n+n)*powers x^(2*(n+n)))):
    ‖leftDerivs (a.hymn T u q d k f' Γ U) l V‖ ≤ z*(1+t^(n+n)* AnalyticBridge.LocalGaussian.Moments.meter (heads G B S.patch.L X r x) 0 D.K (2*(n+n))):=by
   let j:=2*(n+n)
   obtain ⟨hW,hI,hL⟩:= opaqueE q d k a U he hf hp hY hu hΓ hV l hl
   let Q:=a.twilight k T V; have ha:=he.cantos (k:=k) a hV hY hp
   have hq:=D.peak
   rw [← Complex.norm_real,hL]; apply (norm_integral_le_integral_norm ..).trans
   obtain ⟨hM,hy⟩:= purchased ∅ (zero_lt_one.trans_le hq) ha.pos ha.peak j
   change Integrable (fun z=> slopeEnvelope ∅ D.K j z) _ at hM
   simp only [slopeEnvelope,load,Finset.sum_empty,mul_zero,Real.exp_zero,mul_one,Finset.card_empty] at hM hy
   have hT := ((integrable_const (1:ℝ)).add (hM.const_mul (t^(n+n)))).const_mul z
   calc
     _ ≤ ∫ y,z*(1+t^(n+n)*powers y^j) ∂(Gaussian.cloud Q):= integral_mono hI.norm hT hh
     _ ≤ _:=by rw [integral_const_mul,integral_add (integrable_const _) (hM.const_mul _), integral_const,integral_const_mul,probReal_univ,one_smul]; apply mul_le_mul_of_nonneg_left _ hz; gcongr; exact hy.trans (meter_mono (by positivity) _ (a.viewed hY B hp _))

include hτ
lemma huge (hs: ¬ Short S B X)(l:List (Directions G c))(hl:l.length≤n)(hb:∀ A∈l,P.dirBound (S.ratio.parent o) A):
    ‖leftDerivs (a.hymn T u q d k f' Γ U) l V‖ ≤ τ* returnFee C D P B S.patch.L X r x u:=by
   let ρ:= rust C D P B S.patch.L X r x u
   have he:= Peak.frozen q d k a U he hf hp hY hu hΓ hV (beat C*τ) l hl ρ (rust_nn hu) (mul_nonneg (beat_nn C) hτ.1) (coarseWave q d k a U he hf hp hY hu hΓ hV hτ hs l hl hb)
   refine he.trans_eq ?_; unfold returnFee ρ; rw [show Lute.decay B S.patch.L X=1 from if_neg hs]; ring
variable {b : ℕ} {M : ℝ} (hS: Short S B X) (hk:b+1 ≤ n) (hg: glider G T b B.power (2*C.C) M)(ht:1≤ M)(hl: lit o X f' b)
def wage (b:ℕ) (C:Libretto G n) (D:Record)(P B:BudgetPoint)(L:Side)(X:Support f)(r:ℕ)(x u:ℝ):=
    trancheD b L n D.Q (loom P (JointLoad.Heir.reach x) C.C) u B.threshold + Lute.scratch (n:=n) G D P B L X r x

def tariff (n:ℕ)(M:ℝ):= 1+n*2+M -- explicit cast 2 defaults ℝ via M?
def poleSum (b:ℕ)(Q:Rights G n)(M:ℝ):= (tariff n M +tariff n M)^(n+n)*tinyR b Q
def sale (b:ℕ)(Q': Rights G n)(C:Libretto G n) (K:ℝ)(D:Record)(P B:BudgetPoint)(L:Side)(X:Support f)(r:ℕ)(x u:ℝ):= (poleSum b Q' K*((L.val:ℝ)⁻¹)^(b+1)) *(1+ (wage b C D P B L X r x u)^(n+n)*AnalyticBridge.LocalGaussian.Moments.meter (heads G B L X r x) 0 D.K (2*(n+n)))
omit he hf hp hY hu hΓ hV hτ in
lemma wage_pos (b:ℕ)(C:Libretto G n)(D:Record)(P B:BudgetPoint)(L:Side)(X:Support f)(r:ℕ)(x u:ℝ)(hu:0≤u):0≤wage b C D P B L X r x u:=add_nonneg (trancheD_nn b _ _ (zero_le_one.trans D.majorant) hu B.threshold_pos.le) (Lute.scratch_nn n) --syntax
omit hV hp hY hΓ hu hf he hτ [DecidableEq ι] in
include a in
private lemma perch_le (hw : Walled S X Y x r)(ho:o∈X)(hu:0≤u)(z:Prices G ι)(hm:1≤M): 1+Carillon.speed n D.Z B.threshold P.power (scope B X r x) z ≤ tariff n M+wage b C D P B S.patch.L X r x u*(powers z)^2:=by
   let K:= cup (n:=n) D P B X r x; have h₁ :1≤K:= canopy_one D.chimes _ _ _; have hg:= grows z
   have hp : Carillon.pitch n (ι×G.ColorIndex) D.Z (scope B X r x) P.power z≤ ((heads G B S.patch.L X r x:ℕ):ℝ)^2*(K+1)*K*(powers z)^2:=by
     unfold Carillon.pitch; change _*(K+‖z‖^2)*_≤_
     have hi : ‖z‖^2≤powers z^2:= pow_le_pow_left₀ (norm_nonneg _) ((tape_control z).1.trans (tape_control z).2) _
     calc
       _ ≤ ((heads G B S.patch.L X r x:ℕ):ℝ)^2*((K+1)*powers z^2)*K:=by
         gcongr ?_^2 * ?_ * _
         · exact Nat.cast_le.mpr (a.viewed hw B ho G)
         rw [add_mul,one_mul]; exact add_le_add (le_mul_of_one_le_right (by positivity) (one_le_pow₀ hg)) hi
       _=_:=by ring
   have hx : wage b C D P B S.patch.L X r x u ≥ scratch (n:=n) G D P B S.patch.L X r x := le_add_of_nonneg_left (trancheD_nn b _ _ (zero_le_one.trans D.majorant) hu B.threshold_pos.le)
   have hT:= mul_le_mul_of_nonneg_left hp (mul_nonneg (Nat.cast_nonneg n (α:=ℝ)) B.threshold_pos.le)
   have H:=mul_le_mul_of_nonneg_right hx (sq_nonneg (powers z)); unfold scratch at H; change _*_*_*(_+1)*K*_ ≤ _ at H
   unfold Carillon.speed tariff; nlinarith only [hT,H,hm]

include hS hg hk ht hl
private lemma maskRat (Q:Rights G n)(l: List (Directions G c))(hs:l.length≤ n)(hb:∀ A∈l,P.dirBound (S.ratio.parent o) A)(z:Prices G ι):
    let ρ:= wage b C D P B S.patch.L X r x u
    let t:=τ*poleSum b Q M
    ‖leftDerivs (a.concert T u q d k f' Γ U V z) l V‖ ≤ t*((S.patch.L.val:ℝ)⁻¹)^(b+1) * (1+ρ^(n+n)*powers z^(2*(n+n))):=by
   intro ρ t
   let u1:= loom P (reach x) C.C; let L:= (S.patch.L.val:ℝ); let A' :=lumen b M Q S.patch.L X P B C D x u z
   let v:=tinyR b Q; let w:= trancheD b S.patch.L n D.Q u1 (u*‖tape z‖) B.threshold; have hh:A'=v*(M+w)^n*L⁻¹^(b+1):=by unfold A' v L lumen w u1; ring -- order
   have hw :0≤w:= trancheD_nn _ _ _ (zero_le_one.trans D.majorant) (mul_nonneg hu (norm_nonneg _)) B.threshold_pos.le
   have hV' :1 ≤ M+w:= ht.trans (le_add_of_nonneg_right hw); have hv :0≤v:=by have hj:= patterns_nonneg n; have h:= Q.large; unfold v tinyR; positivity
   have hL:0<L:=by unfold L; positivity
   have hy:0≤τ:= hτ.1; have hp' : 0≤ A':=hh.symm ▸ (show 0≤v*(M+w)^n*L⁻¹^(b+1) by positivity)
   have hX:= Peak.allotted q d k a U he hf hp hY hu hΓ hV z (A'*τ) (mul_nonneg hp' hy)
     (fun h i hi l h'=> (Peak.creek (q:=q) (k:=k) (d:=d) he a hf hp hτ hu hV U z (hΓ.stay z h) Q hS hl hk hi h' hg ht).2 _ hi)
   let f:= tariff n M; have hf:1≤f:=by unfold f tariff; linarith only [ht,Nat.cast_nonneg (α:=ℝ) n]
   have hρ:0≤ρ:=wage_pos _ _ _ _ _ _ _ _ _ _ hu -- syntax
   let p:=powers z; let m':= f+ρ*p^2; have hm':1≤ m':= hf.trans (le_add_of_nonneg_right (mul_nonneg hρ (sq_nonneg p)))
   have hq : w ≤ ρ*p^2:=by
     have hA:= grows z; have hq: 1 ≤ p^2:=one_le_pow₀ hA
     have hb:= le_mul_of_one_le_right (mul_nonneg ((by have hQ:=D.majorant; positivity : (0:ℝ) ≤ 2*D.Q).trans (clinicFee_le n (zero_le_one.trans D.majorant))) (sq_nonneg u1)) hq -- uses D.majorant
     apply le_trans (b:= trancheD b S.patch.L n D.Q u1 u B.threshold * p^2) ?_ (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (scratch_nn n)) (sq_nonneg _))
     unfold w trancheD
     have hs:‖tape z‖≤p^2 := (tape_control z).2.trans (le_self_pow₀ hA two_ne_zero)
     calc
       _ ≤ (clinicFee n D.Q*u1^2*p^2 + u*p^2)/B.threshold*(S.patch.L.val:ℝ)^(b+1) := by have h:=B.threshold_pos; gcongr
       _ = _:=by ring
   calc
     _ ≤ A'*τ*m'^n:= (hX.caps _ hs hb).trans (mul_le_mul_of_nonneg_left ((pow_le_pow_left₀ hX.sane (perch_le (a:=a) hY hp hu z ht) _).trans (pow_le_pow_right₀ hm' hs)) (mul_nonneg hp' hy))
     _ ≤ (v*m'^n*L⁻¹^(b+1))*τ*m'^n:= by rw [hh]; gcongr; exact add_le_add (le_add_of_nonneg_left (by positivity)) hq
     _ = (v*τ*L⁻¹^(b+1))*m'^(n+n):=by rw [pow_add]; ring
     _ ≤ (v*τ*L⁻¹^(b+1))*((f+f)^(n+n)*(1+ρ^(n+n)*p^(2*(n+n)))):=mul_le_mul_of_nonneg_left (thickness n hf hρ) (by positivity)
     _ = _:=by unfold t poleSum f L; unfold p v; ring
lemma tinyBill (Q:Rights G n)(l: List (Directions G c))(hs:l.length≤ n)(hb:∀ A∈l,P.dirBound (S.ratio.parent o) A):
    ‖leftDerivs (a.hymn T u q d k f' Γ U) l V‖ ≤ τ*sale b Q C M D P B S.patch.L X r x u:=by
   let ρ:= wage b C D P B S.patch.L X r x u
   have hz : 0≤poleSum b Q M:=by unfold poleSum tinyR tariff; have he:=Q.large; have ht:=patterns_nonneg n; positivity
   exact (Peak.frozen q d k a U he hf hp hY hu hΓ hV _ l hs ρ (wage_pos _ _ _ _ _ _ _ _ _ _ hu) (mul_nonneg (mul_nonneg hτ.1 hz) (by positivity : 0≤((S.patch.L.val:ℝ)⁻¹)^(b+1))) (maskRat q d k a U he hf hp hY hu hΓ hV hτ hS hk hg ht hl Q l hs hb)).trans_eq (by unfold ρ sale; ring)
end YM.PhysicalNext.Repeat.Peak
