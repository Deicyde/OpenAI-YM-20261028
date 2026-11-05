import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Peak.Tansy
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Peak
open Filter Function Lattice Wilson Pressure RG Tree Precision Next Next.Free Next.SectorChange Rows Exterior Bloch
    Planned.AtomRegular MeasureTheory Extra.Iteration Extra.Iteration.Scales SelectedOrderedKernels.Sector
    AnalyticBridge.LocalGaussianLaws JointLoad JointLoad.Heir Lute
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {f c : Side} {L : Side} {P B : BudgetPoint} {x u a t K : ℝ} {b n r : ℕ} {C : Libretto G n} {D : Record}{X:Support f}

-- An additional Plented receipt. same Coverage positions.
def plane (b:ℕ) (C : Libretto G n) (D : Record) (L : Side) := Lute.boost C D L * ((L.val:ℝ)^(b+1))
lemma plane_pos : 0 ≤ plane b C D L := mul_nonneg (boost_nn C D L) (by positivity)
def Rented (b:ℕ)(C : Libretto G n)(D:Record)(P B : BudgetPoint)(L:Side)(r:ℕ)(x u:ℝ) := ((plane b C D L* Lute.ζ B u)^(n+n)*Lute.guests G D.K n L)*((r+48:ℝ)*(1+(radiusB x:ℝ)))^Lute.debited n P.power ≤1
lemma shadow (hu:0≤u)(hb:B.B ≤ 2*radiusB x)(ht : P.threshold≤2*B.threshold):
    wage b C D P B L X r x u ≤ plane b C D L* Lute.ζ B u*Lute.bulk (coverNumber B.B X) r x ^ Lute.fuse n P.power:=by
    let s:= (L.val:ℝ); let v:= s^(b+1); let e:= Lute.ζ B u; let P':= C.C; let z:= loom P (JointLoad.Heir.reach x) C.C
    have hp:1≤ s:=Nat.one_le_cast.mpr L.property; have hV:1≤v:=one_le_pow₀ hp
    have H:=booster (G:=G) (L:=L) (X:=X) (C:=C) (D:=D) (r:=r) hb ht hu
    let A:=scratch (n:=n) G D P B L X r x
    have hx:0≤A:=scratch_nn n; let p:=(clinicFee n D.Q*z^2+u)/B.threshold
    have h:0≤p:=div_nonneg (add_nonneg (mul_nonneg ((mul_nonneg zero_le_two (zero_le_one.trans D.majorant)).trans (clinicFee_le n (zero_le_one.trans D.majorant))) (sq_nonneg _)) hu) B.threshold_pos.le
    let x':= rust C D P B L X r x u
    have hx': x'≥ p*s^3 + A:= by unfold x' Lute.rust; rw [add_assoc]; exact le_add_of_nonneg_left (segment_nn n X P B D.majorant C.matins)
    change p*v+A≤ (boost C D L*v)* _*_
    calc
      _ ≤ (p*s^3 + A)*v := by rw [add_mul]; exact add_le_add (mul_le_mul_of_nonneg_right (le_mul_of_one_le_right h (one_le_pow₀ hp)) (zero_le_one.trans hV)) (le_mul_of_one_le_right hx hV)
      _ ≤ _ := (mul_le_mul_of_nonneg_right (hx'.trans H) (zero_le_one.trans hV)).trans_eq (by ring)

lemma wrapR (hu : 0 ≤ u) (hb:B.B≤2*radiusB x)(ht:P.threshold≤2*B.threshold)(hp:Rented b C D P B L r x u):
    wage b C D P B L X r x u^(n+n)* AnalyticBridge.LocalGaussian.Moments.meter (heads G B L X r x) 0 D.K (2*(n+n))≤ (1+(coverNumber B.B X:ℝ))^Lute.debited n P.power:=by
    let A:= ((r+48:ℝ)*(1+(radiusB x:ℝ))); let d :ℝ:=coverNumber B.B X; let H:=Lute.debited n P.power; let s := Lute.bulk (coverNumber B.B X) r x; have hs:1≤ s:=Lute.bulk_one ..
    let K := plane b C D L * Lute.ζ B u; have hK:0≤K:=mul_nonneg plane_pos (add_nonneg B.threshold_pos.le (div_nonneg hu B.threshold_pos.le))
    have hm :0≤AnalyticBridge.LocalGaussian.Moments.meter (heads G B L X r x) 0 D.K (2*(n+n)):=by unfold AnalyticBridge.LocalGaussian.Moments.meter AnalyticBridge.LocalGaussian.Moments.inflate; have := D.peak; positivity
    have he:= fares (n:=n) (G:=G) (L:=L) (r:=r) (X:=X) (D:=D) hb
    calc
      _ ≤ (K*s^Lute.fuse n P.power)^(n+n)*(guests G D.K n L*s^visitors n) := mul_le_mul (pow_le_pow_left₀ (wage_pos _ _ _ _ _ _ _ _ _ _ hu) (shadow hu hb ht) _) he hm (by positivity)
      _ = ((K^(n+n)*guests G D.K n L)*A^H)*(1+d)^H := by unfold H Lute.debited; change (K*(A*(1+d))^Lute.fuse n P.power)^_*(_*(A*(1+d))^visitors n) = _; simp only [mul_pow (a:=A),mul_pow (a:=K),pow_add];ring
      _ ≤ _:=mul_le_of_le_one_left (by unfold d; positivity) hp
lemma tinypos (b:ℕ)(Q:Rights G n):0≤ Peak.tinyR b Q:=by unfold Peak.tinyR; have hs:=patterns_nonneg n; have he:=Q.large; positivity
lemma polepos (b:ℕ)(Q:Rights G n){M:ℝ}(hQ:0≤M):0≤poleSum b Q M:=by unfold poleSum tariff; have hs:=tinypos b Q; positivity
lemma swirls (M:ℝ)(Q:Rights G n)(hQ:0 ≤ M)(hu:0 ≤ u)(hb:B.B≤2*radiusB x)(ht:P.threshold ≤2*B.threshold)(h:Rented b C D P B L r x u): sale b Q C M D P B L X r x u ≤ (poleSum b Q M*((L.val:ℝ)⁻¹)^(b+1))*(2*(1+(coverNumber B.B X:ℝ))^Lute.debited n P.power):=by
    unfold sale; apply mul_le_mul_of_nonneg_left _ (mul_nonneg (polepos b Q hQ) (by positivity)); rw [two_mul ((1+(coverNumber B.B X:ℝ))^(Lute.debited n P.power))]; exact add_le_add (one_le_pow₀ (by simp))  (wrapR hu hb ht h)
lemma floats (b:ℕ) (C : Libretto G n) (D : Record) (L : Side) (r p : ℕ) (hn : 0 < n) : ∀ᶠ x : ℝ in atTop, ∀ β, betaF G x L/2 ≤ β →
    0<coupling β ∧ ∀ P B : BudgetPoint, B.threshold=fiery G x L → P.power=p → Rented b C D P B L r x (coupling β) := by
  let a := G.slopeConstant*Real.log (L.val:ℝ)
  let d := Lute.debited n p; let H := plane b C D L; let K := Lute.guests G D.K n L
  have hH : 0≤H := plane_pos; have hK : 0≤K := Lute.guest_nn ..
  obtain ⟨v,hv,hv'⟩ : ∃ v > (0:ℝ), (H*v)^(n+n)*K ≤ 1 := by
    have h : Continuous (fun y : ℝ => (H*y)^(n+n)*K) := by fun_prop
    obtain ⟨z,h1,h2⟩ := Metric.mem_nhds_iff.mp ((h.tendsto 0).eventually (ge_mem_nhds (by simp [zero_pow (by omega : n+n≠0)] : (H*0)^(n+n)*K<1)))
    exact ⟨z/2,half_pos h1,h2 (Metric.mem_ball.mpr (by simpa [abs_of_pos h1] using half_lt_self h1))⟩
  let Z (x : ℝ) := ((r+48:ℝ)*(1+(radiusB x:ℝ)))^d
  have hu : Tiny (fun x => meter (x+a)) Z := ((Tiny.const (Tiny.grow a) (r+48:ℝ) (by positivity)).mul (Tiny.cover a) (Tiny.grow a)).pow (Tiny.grow a) d
  have hT := ((flowering a d).const_mul ((r+48:ℝ)^d)); rw [mul_zero] at hT
  filter_upwards [eventually_gt_atTop (-a),((tendsto_rpow_atTop (y:=(1/2:ℝ)) (by norm_num)).comp (Tiny.grow a)).eventually_ge_atTop (4/v),hu (1/2) (by norm_num),hT.eventually (ge_mem_nhds (half_pos hv))] with x hx hy hq hf β hβ
  let y := x+a; have hz : 0<y := by unfold y; linarith
  have hβ : y ≤ 2*β := by change y/2 ≤ _ at hβ; linarith
  have hβ' : 0 < β := by linarith
  refine ⟨coupling_pos hβ',fun P B hB hp => ?_⟩
  let w := coupling β
  have hw : 0 ≤ Lute.ζ B w := add_nonneg B.threshold_pos.le (by have := coupling_pos hβ'; have := B.threshold_pos; unfold w; positivity)
  have hZ : 1≤ Z x := one_le_pow₀ ((show 1 ≤ _ by linarith [Nat.cast_nonneg (α:=ℝ) r] : (1:ℝ)≤r+48).trans (le_mul_of_one_le_right (by positivity) (by simp)))
  have he : coupling β ≤ 2*coupling y := by
    unfold coupling; rw [← div_eq_mul_inv, inv_le_iff_one_le_mul₀ (Real.sqrt_pos.mpr hβ'),div_mul_eq_mul_div,le_div_iff₀ (Real.sqrt_pos.mpr hz),one_mul]; nlinarith [Real.sq_sqrt hz.le, Real.sq_sqrt hβ'.le, Real.sqrt_nonneg β]
  have hV : coupling β / B.threshold * Z x ≤ v/2 := by
    have hh : B.threshold = coupling y * meter y := hB
    have hY := coupling_pos hz
    rw [div_mul_eq_mul_div,div_le_iff₀ B.threshold_pos,hh]; apply (mul_le_mul he hq.2 hq.1 (by positivity)).trans
    have hsq : meter y^(1/2:ℝ)*meter y^(1/2:ℝ)=meter y := by rw [← Real.rpow_add (meter_pos y)]; norm_num
    have h' := mul_le_mul_of_nonneg_right ((div_le_iff₀ hv).mp hy) (show 0 ≤ meter y^(1/2:ℝ) from Real.rpow_nonneg (meter_pos y).le _)
    change _ ≤ meter y^_*v*(meter y^_) at h'; rw [mul_right_comm _ v,hsq] at h'
    nlinarith only [mul_le_mul_of_nonneg_right h' hY.le]
  have hf : B.threshold * Z x ≤ v/2 := by unfold Z; rw [hB,mul_pow]; linarith only [show (r+48:ℝ)^d*((1+(radiusB x:ℝ))^d * fiery G x L) ≤ v/2 from hf]
  unfold Rented; rw [hp]; change ((H*_)^(n+n)*K)*Z x≤1
  have hQ : Lute.ζ B w * Z x ≤ v := by unfold Lute.ζ; rw [add_mul]; linarith
  calc
    _ ≤ ((H*Lute.ζ B w)^(n+n)*K)*(Z x)^(n+n) := mul_le_mul_of_nonneg_left (le_self_pow₀ hZ (by omega)) (by positivity)
    _ = (H*(Lute.ζ B w*Z x))^(n+n)*K := by rw [mul_right_comm,←mul_pow,mul_assoc]
    _ ≤ _ := (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (mul_nonneg hH (mul_nonneg hw (zero_le_one.trans hZ))) (mul_le_mul_of_nonneg_left hQ hH) _) hK).trans hv'

end YM.PhysicalNext.Repeat.Peak
