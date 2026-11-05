import YM.Contacts.Harvest.Lined
/-!
# Recursive absolute integral through one parent

Records estimate and equality of integrals both with and without fixing the other arms and/or
slices of disjoint groups. This is the ABS estimate in the nonperturbative regimes. No assertions
on transition between PT regulators. Allows obtaining annular distribution pairings in any such
arm (root projection or root residue). No subtraction by detector applied to positive correl on
an overlapping normal test.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Contacts.Harvest.Route
open Function Filter Set Metric MeasureTheory Submodule Table Spec Normal MultipleContact OPE Layers Ordered
open scoped Topology Classical BigOperators ContDiff InnerProductSpace MeasureTheory
variable {E X W I : Type}[NormedAddCommGroup E][InnerProductSpace ℝ E][FiniteDimensional ℝ E]
 [NormedAddCommGroup X][NormedSpace ℂ X]
variable {G: Gauge} {C: Family G}{F: Extraction.Order}{S : Table C.book} {Z: Final C F S}
variable {k : ℕ} {d : Fin k→ℕ}{g : Normal.Group k} {P : E→ₗᵢ[ℝ] Points k} {Q : Pieces g} {γ : ℝ}
variable (r : Route P Q I W) (M : Devices Z.sector.derivatives) (T : W→ Cells S d) (D : Reader E W X k Z.sector.derivatives)
local notation "GN" => Normal.Group k
variable (i : Q.parts) (b : Way d i.val) (u:Fans P i.val) (v:Splittings i.val)
variable {w : W} {z : SmoothTests E} {a c : ℝ} {B : W→ℝ}

-- root branch paired BEFORE net (expects appropriate punctured test). An arm of the election read against post-Taylor-difference test. Still all other groups along for the estimate.
def select (f : Menu k) (w:W) (z : SmoothTests E) := scoreAt D w z ((r.components M T w).absentee P (r.length w) f Q i (fun x=>wind M d i.val b (r.oculus w i.val x)))
def hail (f : Menu k) (w:W) (z : SmoothTests E) (a : ℝ) := r.select M T D i b f w (r.target i b u v w z a)
/-- annular pairing with the root choice at group i already fixed. -/
def beckon (f : Menu k)(w : W)(z : SmoothTests E)(n : ℕ) := r.select M T D i b f w (mask (eclipse (normalOn P i.val) (dyad n)) (r.net i b w z))
lemma selected_nil (f : Menu k)(w) : r.select M T D i b f w 0=0:= by
   unfold select scoreAt; funext x; change D w x (under x _ 0)=(0:X); rw [map_zero,map_zero]
lemma selected_many {F : Type*} (f : Menu k)(w) (L : Finset F)(z:F→ SmoothTests E) (x:E) : r.select M T D i b f w (∑ j∈ L,z j) x= ∑ j∈ L,r.select M T D i b f w (z j) x := map_sum ( (D w x).comp (Normal.under x ((r.components M T w).absentee P (r.length w) f Q i (fun x=> wind M d _ b (r.oculus w i.val x))))) z L
lemma splitted (f w z n y) : r.beckon M T D i b f w z n y= ∑ v:Splittings i.val, r.hail M T D i b u v f w z (dyad n) y := by unfold beckon hail target; rw [← u.ray_sums _ (dyad_pos _), selected_many]
variable (h : 1 < i.val.card)
lemma treated (w : W) : (r.components M T w).treatment i.val b= (fun x=>wind M d i.val b (r.oculus w i.val x)):= funext (fun x=> r.core_wind M T _ i.val x b)
lemma held (f : Menu k)(z : SmoothTests E) (w : r.ramp i (outward b) u v) (hz: tsupport z.val⊆ r.stage w.val.1) (x:E):
   r.hail M T D i b u v f w.val.1 z w.val.2 x= (r.renew i (outward b) u v h).windings M (r.listener M i b u v D) (fun p : r.ramp i (outward b) u v=> T p.val.1) (widenMenu v f)
       w (r.target i b u v w.val.1 z w.val.2) x:= by
    unfold hail select windings scoreAt; rw [System.in_splitting (U:=v) (hx:=r.displaysNormals i.val i.property) (he:=(r.targets i b u v w.property.1.1 hz).trans ((r.sun_shade ..).trans (u.lights (r.displaysNormals i.val i.property) v w.property.1.1)))]; rfl

variable [MeasureSpace E][BorelSpace E][(volume:Measure E).IsAddHaarMeasure]
variable [Fintype I]
-- step at just one normalized angular fan patch. Records constant independent of shell scale and Menu.
omit [BorelSpace E] [(volume:Measure E).IsAddHaarMeasure] in
lemma retold (hB : ∀ w,0<B w)(hh: Economy Q γ) {C:ℝ}(hc : 0<C)
  (hf : Achieves Z M (r.renew i (outward b) u v h) (fun p=>T p.val.1) (r.promise i b u v B) (r.listener M i b u v D) γ C) : ∃ A>(0:ℝ),∀ (f:Menu k) (w:W)(z:SmoothTests E) (a:ℝ), a∈ Ioc 0 1 → ∀ c:ℝ,
       tsupport z.val ⊆ r.stage w → Jet (stairs d Q) univ (composed (r.frame w) z).val c →
          Dust (r.hail M T D i b u v f w z a) (A*c*r.bag d B w (generosity Q γ)* a^γ*behind Q i f γ):= by
    obtain ⟨K,hK,hℱ⟩:= r.sufficient i b u v h; let q:= replace i v.val; let F:=r.marginFactor i (d:=d); have hF:0<F:= zero_lt_one.trans_le (r.margin_pos i); have he:= zero_lt_one.trans_le hK; refine ⟨C*K*F,by positivity,fun f w z a ha c hz hx=>?_⟩
    let k':= r.bag d B w (generosity Q γ); let L:= a/r.R i.val w; let p:=behind Q i f γ;
    have hm:=hx.pos
    by_cases hS : (r.site i (outward b) u v w a).Nonempty; swap
    · unfold hail; rw [r.no_target _ _ _ _ ha.1 hz hS,selected_nil]; have hk:0< k':= r.bag_pos w d (hB w) -- parsing ..
      have hl:0<a:= ha.1; have hp:0<p:= behind_pos ..; apply Dust.zero; change 0≤ C*K*F*c*k' *_ *p; positivity
    let t:r.ramp i (outward b) u v:= ⟨(w,a),ha,hS⟩; let R':= r.renew i (outward b) u v h
    have ht:=r.seat i u v b hh h hB t f; let X:= R'.bag d (r.promise i b u v B) t (generosity q γ) * shadow q (widenMenu v f) γ; have hX : X * tailPay b L ≤ F*k'*a^γ * p:=ht
    rw [show r.hail M T D i b u v f w z a=_ from funext (r.held M T D i b u v h f z t hz)]
    apply Dust.mono (hf.estimates (widenMenu v f) t _ (r.targets i b u v ha.1 hz) (hℱ t z hz hx))
    change C*(K*c*tailPay b L)* R'.bag d _ t _ *shadow _ _ _≤ C*K*F*c*k' *_ *p; calc
       _ = (C*K*c)*(X*tailPay b L):= by unfold X; ring
       _ ≤ (C*K*c)*(F*k'*a^γ*p) := by gcongr
       _ = _:= by ring

omit [BorelSpace E] [(volume:Measure E).IsAddHaarMeasure] in
lemma cost_one (hB : ∀ w,0<B w)(hh: Economy Q γ)
  (hy : ∀ v:Splittings i.val, ∃ C>(0:ℝ), Achieves Z M (r.renew i (outward b) u v h) (fun p=>T p.val.1) (r.promise i b u v B) (r.listener M i b u v D) γ C) : ∃ C>(0:ℝ),∀ (f:Menu k) w (z:SmoothTests E)(c:ℝ), tsupport z.val ⊆ r.stage w → Jet (stairs d Q) univ (composed (r.frame w) z).val c → ∀ n,
            Dust (r.beckon M T D i b f w z n) (C*c*r.bag d B w (generosity Q γ)* (dyad n)^γ*behind Q i f γ) := by
   choose A hA hT using fun v:Splittings i.val=> r.retold M T D i b u v h hB hh (hy v).choose_spec.1 (hy v).choose_spec.2; let C':= ∑ i,A i; let L:=max 1 C'; have hL:0<L:= zero_lt_one.trans_le (le_max_left ..)
   refine ⟨L,hL,fun f w z c hp hF t=>?_⟩; have ha:0<dyad t:= dyad_pos t; have hh:=Dust.finite Finset.univ fun i hi=> hT i f w z (dyad t) ⟨ha,dyad_le t⟩ c hp hF
   rw [funext (r.splitted M T D i b u f w z t)]; apply hh.mono; have hc:=hF.pos; have hb:0< r.bag d B w (generosity Q γ):= r.bag_pos w d (hB w); have he:0< behind Q i f γ := behind_pos ..; simp_rw [← Finset.sum_mul]; gcongr; exact le_max_right ..
omit [Fintype I] in
/-- Annular sum irrespective of any other group's election. Requires actually testing in the aperture. -/
lemma emerges (hz : tsupport z.val ⊆ r.stage w)(f : Menu k)
   : ∀ᵐ x:E,∀ᶠ n in (atTop:Filter ℕ), (∑ j∈ Finset.range n,r.beckon M T D i b f w z j x)=r.select M T D i b f w (r.net i b w z) x:= by
   let K:= normalOn P i.val; let q:= r.net i b w z; let V(j:ℕ):= mask (eclipse K (dyad j)) q; let Y:= r.components M T w; let F(t):= wind M d i.val b (r.oculus w i.val t)
   filter_upwards [ Y.announces P (r.length w) Q i f (r.displaysNormals i.val i.property) F (h:= fun x hx=> reunion K q (r.halo_small i b hz) hx) ] with x hx; filter_upwards [hx] with n hn
   change ∑ j∈ Finset.range n,r.select M T D i b f w (V j) x=_; rw [← selected_many]; exact congrArg (D w x) hn

/- the actual estimate on an arm already includes current ballots admitting arbitrary partial Taylor timing -/
include h
variable [CompleteSpace X]
lemma pass (L : ℝ)(hL : 0<L) (hh : Economy Q γ)
  (hy : ∀ (f:Menu k) w (z:SmoothTests E)(c:ℝ), tsupport z.val⊆ r.stage w → Jet (stairs d Q) univ (composed (r.frame w) z).val c → ∀ n,Dust (r.beckon M T D i b f w z n) (L*c*r.bag d B w (generosity Q γ)* (dyad n)^γ*behind Q i f γ)) (hB:∀ w,0<B w): ∃ C >(0:ℝ), ∀ (f:Menu k) w (z:SmoothTests E)(c:ℝ), tsupport z.val⊆ r.stage w → Jet (stairs d Q) univ (composed (r.frame w) z).val c →
    Dust (r.select M T D i b f w (System.sliceAt P i.val (f i.val).slice (r.net i b w z))) (C*c*r.bag d B w (generosity Q γ)* shadow Q f γ):= by
   let H(n:ℕ):= (dyad n)^γ; let X:=∑' n:ℕ,H n; let V:=max 1 X; have hV:1≤V:= le_max_left ..; have hh':= geometric_dyadic hh.pos; have hP:0<V:=zero_lt_one.trans_le hV;
   refine ⟨L*V,mul_pos hL hP,fun f w z c hp he=>?_⟩; let B':= r.bag d B w (generosity Q γ); let C':= L*c*B'; let t:= behind Q i f γ; have hvL : Summable (fun n=> C'*H n*t):= (hh'.mul_left C').mul_right t
   have hc:=he.pos; have ht:0<t:=behind_pos Q i f; have hb : 0<B':= r.bag_pos w d (hB w); have hX:0≤C':= mul_nonneg (mul_nonneg hL.le hc) hb.le
   specialize hy f w z c hp he; rw [from_behind i, kick,if_neg (not_le.mpr h)] -- shadow & kick unfolds
   cases hb' : (f i.val).slice with
   | some n=> apply (hy n).mono; change C'* H n*t ≤ L*V*c*B'*(t*H n); have hℝ:0<H n:= Real.rpow_pos_of_pos (dyad_pos _) _; apply le_trans (le_mul_of_one_le_right (show 0≤ C'* H n*t by positivity) hV); apply le_of_eq; unfold C'; ring
   | none=> apply (Dust.reunites hvL hy (r.emerges M T D i b hp f)).1.mono; change ∑' j,C'*H j*t ≤ L*V*c*B'*(t*1); rw [tsum_mul_right,tsum_mul_left]; exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (show (∑'j,H j) ≤ V from le_max_right ..) hX) ht.le).trans_eq (by unfold C'; ring)
end YM.Contacts.Harvest.Route
