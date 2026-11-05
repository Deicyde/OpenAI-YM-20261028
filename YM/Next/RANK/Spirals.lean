import YM.Next.RANK.RayGate

/-!
# W polynomial at k supplied before the course

Re-express Taylor at the new threshold on its complete stencil. Take τ actual uses;
log costs in pressure tests still on old unweighted cap. Remainder bound is on every U
on the smaller-threshold footprint, not just on unmarked integral. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Spindle
open Function Filter Set RG Source Wilson Extraction Lattice Labels Perch Configuration Atlas Beamer
open Normal Rise Common Filter Glimmer LiftMark Station Asymptotics MvPolynomial
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff Classical

variable {G : Gauge} {C : Family G}
variable {N p k d nD b i : ℕ} {n : Side}

-- evaluation difference through actual variables
lemma amove {U : Type*} (T : poly U) (D : ℕ) (ht : totalDegree T≤D) (B : ℝ) (hB : 1≤B) (v w : U→ℝ) (hv : ∀ i, |v i| ≤ B) (hw : ∀ i, |w i| ≤ B) (δ : ℝ) (hδ : 0≤δ) (hi : ∀ i,|v i-w i|≤δ) :
    ‖text v T-text w T‖ ≤ coin T*((D:ℝ)*B^D*δ) := by
  let Q (a : U → ℝ) := (MvPolynomial.aeval (R:=ℂ) fun i=> (↑(a i):ℂ))
  let V:=Q v;let W:= Q w
  have hb := zero_lt_one.trans_le hB
  refine Common.to_basis (V.toLinearMap-W.toLinearMap) _ fun i he=> ?_
  obtain ⟨l,hl⟩:= Common.letter i;rw [hl,LinearMap.sub_apply]; let A:= Fin (Finsupp.sum i fun _ i=>i)
  have hg j: ‖V (X (l j))‖≤B ∧ ‖W (X (l j))‖≤B ∧ ‖V (X (l j))-W (X (l j))‖≤δ := by
    unfold V W Q; simp only [aeval_X,Complex.norm_real,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]; exact ⟨hv _,hw _,hi _⟩
  have he' (s : Finset A) : ‖V (glyphs l s)‖ ≤ B^s.card := by
    unfold glyphs; rw [map_prod,norm_prod, ← Finset.prod_const]; exact Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _=> (hg i).1)
  have hx (s : Finset A) : ‖V (glyphs l s)-W (glyphs l s)‖≤s.card * B^s.card * δ := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert j s hj IH =>
      rw [show glyphs l (insert j s)=X (l j)*glyphs l s from Finset.prod_insert hj,map_mul,map_mul]; let p:= glyphs l s
      have H (x y a b:ℂ) : x*a-y*b=(x-y)*a+y*(a-b):=by ring
      rw [H]; apply (norm_add_le ..).trans; rw [norm_mul,norm_mul,Finset.card_insert_of_notMem hj]; apply (add_le_add (mul_le_mul (hg j|>.2.2) (he' s) (norm_nonneg _) hδ) (mul_le_mul (hg j|>.2.1) IH (norm_nonneg _) hb.le)).trans
      push_cast; have hf:= mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hB (Nat.le_succ s.card)) hδ; rw [pow_succ] at hf ⊢; linarith only [hf]
  apply (hx Finset.univ).trans
  have hh : Fintype.card A≤D := by simpa [A] using (MvPolynomial.le_totalDegree he).trans ht
  rw [Finset.card_univ];gcongr

lemma moving (T : poly (links G (0:Site n) b)) (D : ℕ) (ht : totalDegree T≤D) (v w : Space G (0:Site n) b) (hv : ‖v‖≤1) (hw : ‖w‖≤1) :
    ‖text (scan v) T-text (scan w) T‖ ≤ coin T * (D * ‖v-w‖) := by
  convert amove T D ht 1 le_rfl (scan v) (scan w) (fun i => (scan_sum v i).trans hv) (fun i => (scan_sum w i).trans hw) _ (norm_nonneg (v-w)) (fun i => scan_sum (v-w) i) using 1; simp only [one_pow,mul_one]

lemma pure_set (X : ℝ) (p : Word b) (U : Turn b → G.Color) : stage p (X • U)=X • stage p U := by
  induction p with
  | nil => simp [stage]
  | cons i p H =>
    cases hi : i.2 <;> (simp only [stage,List.map_cons,List.sum_cons,hi, ↓reduceIte,Bool.false_eq_true,Pi.smul_apply,smul_add]; unfold stage at H)
    · rw [←H];rfl
    rw [smul_neg,← H];rfl

-- actual evaluation using τ-read. polynomial includes ONLY short site variables; stored footprint important.
def sender {o : Site n} (h : 2*(b+1)<n.val) (t g : ℝ) (B : poly (links G o b)) := factors (↑(g/t):ℂ) (dustAt h B)
def signet (o : Site n) (g : ℝ) (B : poly (slotC G b)) (U : Config G n) := text (fun i => Spindle.curl b U g o i.1 i.2) B
lemma lets {o : Site n} (h : 2*(b+1)<n.val) (t : ℝ) {g : ℝ} (hg : 0<g) (B : poly (links G o b)) (U : Config G n) :
    signet o g (sender h t g B) U=text (scan (rows t h (G.curvature ∘ registered b U o))) B := by
  unfold signet sender; rw [sold_factor]; let p:= curl b U g o; let u:=g/t
  let Q:= sender h t g B
  calc
    _ = text (scan (rows 1 h (u • p))) B := full_dust h (u • p) B
    _ = _ := by apply congr_arg (fun x:Space G o b=> text (scan x) B); funext i
                have hx : u*g⁻¹=t⁻¹ := by dsimp only [u]; rw [div_eq_mul_inv, mul_right_comm]; rw [mul_inv_cancel₀ hg.ne',one_mul]
                rw [show u • p=t⁻¹ • (G.curvature ∘ registered b U o) by
                     ext1 i; change u • (g⁻¹ • _) = t⁻¹ • G.curvature _; rw [smul_smul,hx]]
                rw [rows,pure_set,inv_one,one_smul];rfl

-- The Taylor output read of a short Source even if coarsening would change all objects. Keeps true masks. All paths within complete patch.

lemma issued (S : Rules G) (v : C.label d) (h : Provision C d k N p i b) (t : ℝ) (ht : 0<t) {A : ℝ} {P : poly (Up C k p b)}
    (he : WRead S k N p d b i nD A v P) (hc : C.Makes) (h₁ : C.ref d ≤ k) (h₂ : k ≤ N)
    (U : Config G (C.side k p)) (hu : Healthy t (patch b 0) U) (hy : 4*b*t ≤ S.c) :
    let p':=(C.path.rep N p k).p
    let M:= moneys C d k N p v
    let Q:= P
    let u:=p'.threshold
    let a:ℝ:= 4*b*t
    let r:=2*a/u
    let R:=(S.C+G.colorScale)*a^2/u
    r ≤ pane S → R+r≤1 →
      ‖nearHol C v i k N p U-signet 0 (GaugeScale C k N p) (sender h.length u (GaugeScale C k N p) Q) U‖ ≤
        4*M * r^(nD+1) + expCut p' i*M + coin P*(nD*R) := by
  intro p' M Q u a r R hx hH
  let x:=wired p'.threshold 0 b U; let o:= (0:Site (C.side k p)); let ℓ:= C.side k p
  let X:=rows (o:=o) p'.threshold h.length (G.curvature ∘ registered b U o)
  obtain ⟨ha,hg,hi⟩:= closer S h.length U hu p'.threshold p'.threshold_pos ht hy
  have hv : ‖x‖≤pane S := ha.trans hx
  have hp : Agrees (patch b o) (net p' 0 b x) (spine U 0) := by
    intro j he hp; let i:Dim (0:Site ℓ) b := ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ j,he,hp⟩⟩; exact (net_in p' x i).trans (hg i)
  have He : nearHol C v i k N p U=nearHol C v i k N p (net p' o b x) := by
    apply tsum_congr; intro j
    apply congr_arg
    obtain ⟨s,q,-,⟨a,h₀,hA⟩,-⟩ := he.plans
    have ht := hA.smooth j
    apply (ht.symmetry (fingers U o) U).symm.trans (Eq.symm ?_); apply ht.sites _ _
    intro e ht' he'; exact hp _ (h.contained (h:=hc) (hk:=h₁) (hN:=h₂) v j ht') (h.contained (h:=hc) (hk:=h₁) (hN:=h₂) v j he')
  let N':=net p' o b x; let W:= wideHol C v i k N p N'; let Y:=text (scan x) P
  have hz : flags p'.threshold N'=∅ := voids (occupied p' x S hv) le_rfl
  rw [He,show nearHol C v i k N p N'=awakeFull C k N p v N' - W from eq_sub_of_add_eq (sections_true hc h₁ h₂ p i v N' hz),lets]
  · let f:= awakeFull C k N p v N';let g:= text (scan X) P
    change ‖f-W-g‖≤ _
    rw [show f-W-g=(f-Y-W)+(Y-g) by abel]
    apply (norm_add_le ..).trans; apply add_le_add
    · have hh : 0 ≤ M:= money_nn ..; apply (norm_sub_le ..).trans; apply add_le_add ((beginnings he hc h₁ h₂ x hv).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) ha _) (show 0≤4*M by positivity)))
      obtain ⟨_,_,_,_,e,hv,hs⟩:= he.plans; let E:= wideW C v i k N p
      let Z j:= E j*wideA C v i k N p j N'
      have ht (j : wideIndex C v i k N p) : ‖Z j‖ ≤ ‖E j‖*e j := by
        unfold Z; rw [norm_mul]; exact mul_le_mul_of_nonneg_left ((hs.contact j).2 _ (by unfold Healthy; rw [show _= _ from hz]; simp) [] (Nat.zero_le _) (by simp)) (norm_nonneg _)
      have hE := hs.collects.of_nonneg_of_le (fun i=> norm_nonneg (Z i)) ht
      change ‖∑' i,Z i‖≤_; exact (norm_tsum_le_tsum_norm hE).trans ((hE.tsum_le_tsum ht hs.collects).trans hv.2.2)
    have hg' : ‖X‖≤1:=le_trans (show ‖X‖≤‖X-x‖+‖x‖ from le_trans (le_of_eq (congr_arg norm (sub_add_cancel X x).symm)) (norm_add_le ..))
      ((add_le_add ((norm_sub_rev ..).trans_le hi) ha).trans hH)
    have hd : totalDegree P≤nD := by obtain ⟨P,Q,rfl,⟨_,_,hp⟩,_,_,hh⟩:=he.plans; exact (totalDegree_add ..).trans (max_le hp.produced.choose_spec.1.degree hh.produced.choose_spec.1.degree)
    exact (moving P nD hd x X (hv.trans ((pane_le S).trans (by norm_num))) hg').trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hi (Nat.cast_nonneg nD)) (sign _ _ zero_le_one))
  exact inv_pos.mpr (Real.sqrt_pos.2 (Overlay.beta_positive hc.wilson h₂))

-- τ threshold on the already paid trajectory. At k comparison expenditure floor buys exponent tolerance.
def α₀ (n : ℕ) := shade n/4
lemma alpha_pos (n : ℕ) : 0<α₀ n := by unfold α₀; have h:=shade_pos n; positivity
lemma αpay (n : ℕ) : α₀ n*((n:ℝ)+2) ≤ 1/16 := by unfold α₀; linarith only [shade_thin n]

def tau (P : Levels G) (k : ℕ) := P.clock.hatCoupling k * hot (clim P k)
lemma tau_pos (A : Levels G) (k) : 0 < tau A k := mul_pos (inv_pos.mpr (Real.sqrt_pos.2 (zero_lt_one.trans (A.fits.delayed k)))) (Real.exp_pos _)
lemma hotter (a : ℝ) (h : 0<a) : ∀ᶠ s in atTop, hot s ≤ bill a s := by
  -- exp(y^1.5)
  filter_upwards [y_rate.eventually_ge_atTop ((a⁻¹)^2),y_rate.eventually_ge_atTop 1] with s hs ht
  unfold hot bill; apply Real.exp_le_exp.mpr
  rw [show (3:ℝ)/2=1+1/2 by ring,Real.rpow_add (by linarith only [ht]),Real.rpow_one,← Real.sqrt_eq_rpow]; have he :=Real.sq_sqrt (show 0 ≤ y s by linarith only [ht]); have hp:= Real.sqrt_nonneg (y s)
  have hy : a⁻¹ ≤ Real.sqrt (y s) := by nlinarith only [he,hp,hs]
  have hf : 1 ≤ a * Real.sqrt (y s) := le_trans (inv_mul_cancel₀ h.ne').symm.le ((mul_le_mul_of_nonneg_right hy h.le).trans_eq (mul_comm ..))
  unfold boil; have hY:= mul_le_mul_of_nonneg_right hf hp; apply le_trans (b:= y s*(a* y s)) ?_ (le_of_eq (by ring)); apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans ht); nlinarith only [hY,congr_arg (fun x=>a*x) he]

lemma radius_paid (C : Family G) {a : ℝ} (ha : 0<a) (H : G.Simple) (hp : C.Makes) : ∀ᶠ k in atTop,
    let s:=clim C.path.levels k; let f:= 4*(sizeQ C k:ℝ)*tau C.path.levels k
    2*f/C.path.levels.clock.threshold k ≤ bill (-1+a) s := by
  let P:= C.path.levels; have he:= hat_rate P H
  have hh : ∀ᶠ k in atTop,8* (sizeQ C k:ℝ) ≤ bill (a/2) (clim P k):= by
    filter_upwards [setter C (a/2) (by positivity) 8 H hp 1] with k h
    rw [pow_one] at h; linarith only [h]
  filter_upwards [hh,he.eventually (hotter (a/2) (by positivity))] with k hf hp
  let s:=clim P k
  let v:=tau P k
  let g:=P.clock.hatCoupling k;let t:=P.clock.threshold k
  have hg : 0<g:= inv_pos.mpr (Real.sqrt_pos.2 (zero_lt_one.trans (P.fits.delayed k)))
  have heq : t=g*bill 1 s := congr_arg (g * ·) (fire_bill P k)
  have ht : 0<t := (P.budget k).threshold_pos
  dsimp only; rw [div_le_iff₀ ht]
  change 2*(4*(sizeQ C k:ℝ)*v) ≤ bill (-1+a) s*t
  have hy : bill (-1+a) s*t = g* (bill (a/2) s*bill (a/2) s) := by rw [heq,mul_left_comm,overlap,overlap]; congr 2; ring
  rw [hy]; change 2*(4*(sizeQ C k:ℝ)*(g*hot s))≤_
  linarith only [mul_le_mul_of_nonneg_left (mul_le_mul hf hp (Real.exp_pos _).le (Real.exp_pos _).le) hg.le]

def Ice (q : Rules G) (U t : ℝ) :=
    U ≤ q.c ∧ 2*U/t ≤ pane q ∧ (q.C+G.colorScale)*U^2/t + 2*U/t ≤ 1

lemma iced (S : Rules G) (C : Family G) (Hg : G.Simple) (h : C.Makes) (b : ℝ) : ∀ᶠ k in atTop,
    let a:= 4*(sizeQ C k:ℝ)*tau C.path.levels k
    let t:= C.path.levels.clock.threshold k;let s:=clim C.path.levels k
    Ice S a t ∧ (S.C+G.colorScale)*a^2/t ≤ Perch.bill b s := by
  let P:= C.path.levels; have hv:=hat_rate P Hg; let X := S.C+G.colorScale
  have h₀ : Tendsto (fun k=>Perch.bill (-1+(1:ℝ)/2) (clim P k)) atTop (𝓝 0) := (Perch.bill_hi (by norm_num)).comp hv
  let y:=max 2 (-b+1)
  filter_upwards [booth P y Hg,radius_paid C (by norm_num : 0<(1/2:ℝ)) Hg h,
    h₀.eventually (ge_mem_nhds (lt_min S.radius (pane_pos S))),
    h₀.eventually (ge_mem_nhds (by norm_num : (0:ℝ)<1/4)),hv.eventually (transports
       (show -y < b by have h:=le_max_right (2:ℝ) (-b+1);unfold y; linarith only [h]) X),
    hv.eventually (transports (show -y<0 by have h:=le_max_left (2:ℝ) (-b+1); unfold y; linarith only [h]) (2*X))] with k H1 H2 H3 H4 H5 H6
  intro a t s
  have hz : 0 ≤ a := mul_nonneg (by positivity) (tau_pos _ _).le; have ht : 0<t:=(P.budget k).threshold_pos
  have ht' : t≤ 1 := (P.budget k).threshold_le
  let m:= min S.c (pane S)
  have hm : 0 ≤ m := (lt_min S.radius (pane_pos S)).le
  have hs : 2*a/t ≤ m := le_trans H2 H3
  have hf : 2*a/t ≤ 1/4 := le_trans H2 H4
  have hg : a ≤ S.c := by have hp:= ((div_le_iff₀ ht).mp hs).trans (mul_le_of_le_one_right hm ht'); linarith only [hp,hz,min_le_left S.c (pane S)]
  have hx : a ≤ t := by have hp:= (div_le_iff₀ ht).mp hf; linarith
  have he : a^2/t ≤ t := by rw [div_le_iff₀ ht, sq]; gcongr
  have hX : 0 ≤ X:= add_nonneg S.positive.le G.colorScale_pos.le
  have hr : X*a^2/t ≤ X* Perch.bill (-y) s := by rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left (he.trans H1) hX
  change (a≤ S.c ∧ 2*a/t≤pane S∧X*a^2/t+2*a/t≤1) ∧ X*a^2/t ≤ _
  refine ⟨⟨hg,hs.trans (min_le_right ..),?_⟩,hr.trans H5⟩
  rw [bill_zero] at H6; linarith only [H6,hr,hf]

lemma fusible (S : Rules G) (C : Family G) (c : ℝ) (hc : 0 ≤ c) (d D : ℕ) (Hg : G.Simple) (h : C.Makes) : ∀ᶠ k in atTop,
    ∀ N,k ≤ N→ ∀ p,
      C.ref d ≤ k → year C D k →
      let b:= sizeQ C k;let A:=C.path.levels; let m:=scouts C k; let s:=clim A k
      let g:= GaugeScale C k N p; let V:= C.path.rep N p k
      ∀ w : C.label d, ∀ P, WRead S k N p d b m D (shadow C k p D c) w P→ ∀ u : Provision C d k N p m b,
        ∀ U : Config G (C.side k p), Healthy (tau A k) (patch b 0) U →
          ‖nearHol C w m k N p U - signet 0 g (sender u.length V.p.threshold g P) U‖ ≤ Perch.bill (-(D:ℝ)) s * paid C d k N p w := by
  let A:= C.path.levels;let e:=α₀ D; have hx : 0<e:= alpha_pos _
  have he:= (show e*((D:ℝ)+2)≤1/16 from αpay D)
  let v:= -(D:ℝ);let K:= v-2-2*e; let J:= hat_rate A Hg
  have hi : e+(-1+e)*((D:ℝ)+1)< v:= by unfold v e at *; linarith only [he]
  have hs : e+e+K < v := by unfold K; linarith only
  filter_upwards [J.eventually (transports hi (3*(4:ℝ))),J.eventually (transports (show K+e < v by linarith only [hs,hx]) 3),
    J.eventually (transports hs (3*4*(D:ℝ))),iced S C Hg h K,radius_paid C hx Hg h, shrank C (-K) Hg h,checks C D c e Hg hx] with k h1 h2 h3 H hr hB hv N hN p hR hW
  intro b A' m s g V w P hp u U hU
  obtain ⟨⟨Ho,Hq,Hf⟩,hK⟩:= H
  let r:= 4*(b:ℝ)*tau A k; let B:= A.clock.threshold k; let M:= Perch.bill e s;let Y:=Perch.bill K s
  have hh : (C.path.rep N p k).p.threshold=B:= by rw [(h.wilson.represents N p k hN).vac];rfl
  have hw:= issued S w u (tau A k) (tau_pos A k) hp h hR hN U hU Ho
  dsimp only at hw; rw [hh] at hw; change V.p.threshold=B at hh
  rw [hh]; apply (hw Hq Hf).trans
  let L:= paid C d k N p w
  have hc' : 0 ≤ shadow C k p D c:= by unfold shadow; positivity
  have hy : 0 ≤ L := paid_pos ..; have hm : 0 ≤ moneys C d k N p w:=money_nn ..; have hM : 0 ≤ M:= (Real.exp_pos _).le
  have ht' : 0≤Y:=(Real.exp_pos _).le; have hb : 0≤B := (A.budget k).threshold_pos.le
  have ha : 0≤r:= mul_nonneg (by positivity) (tau_pos ..).le
  have ht := (show moneys C d k N p w ≤ M*L from mul_le_mul_of_nonneg_right hW hy)
  have hd : (2*r/B)^(D+1) ≤ Perch.bill ((-1+e)*((D:ℝ)+1)) s := by
    refine (pow_le_pow_left₀ (show 0 ≤ 2*r/B by positivity) hr (D+1)).trans_eq ?_; rw [Glimmer.bills]; push_cast;rfl
  have ha' : expCut V.p m ≤ Y := by simpa only [neg_neg] using! hB N hN p
  have hP : coin P ≤ 4*(M*L)* M := (tallied hp hc').2.trans (mul_le_mul (mul_le_mul_of_nonneg_left ht (by norm_num)) (hv p) hc' (by positivity))
  change 4*moneys _ _ _ _ _ _* (2*r/B)^(D+1) + expCut V.p m* _ + coin P * (D*((S.C+G.colorScale)*r^2/B)) ≤ _
  apply (add_le_add (add_le_add (mul_le_mul (mul_le_mul_of_nonneg_left ht (by norm_num)) hd (pow_nonneg (by positivity) _) (by positivity)) (mul_le_mul ha' ht hm ht'))
    (mul_le_mul hP (mul_le_mul_of_nonneg_left hK (Nat.cast_nonneg _)) (by have hc:=S.positive; have hc':= G.colorScale_pos; positivity) (by positivity))).trans
  rw [← overlap] at h1 h2; rw [← overlap,←overlap] at h3; dsimp only [M,L,K,Y,v,A,clim] at *; linarith only [mul_le_mul_of_nonneg_right h1 hy,mul_le_mul_of_nonneg_right h2 hy,mul_le_mul_of_nonneg_right h3 hy]
end YM.Next.Rank.Spindle
