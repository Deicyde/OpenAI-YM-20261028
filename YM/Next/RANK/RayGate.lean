import YM.Next.RANK.Carried
import YM.Next.RANK.Inks
import YM.Next.RANK.RailsPrice
import YM.Next.RANK.Walling


/-!
# Actual threshold Taylor receipt

Obtain calibrated Heating on the ARENA of histories whose kernel carries these
κ bounds. Use pin budget *before* normalizing; identity/linear-label coordinates
still in canonical rolled frame. The stage cost `year` must
be paid together with later mixed-trajectory hypotheses.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Spindle
open Function Set Filter Lattice Wilson RG Extraction Source Labels Source.Drops Normal Rise Perch Glimmer Station Price
  Configuration Atlas Beamer LiftMark Tariffs MvPolynomial Asymptotics MeasureTheory
open scoped Classical Topology BigOperators Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} (C : Family G)
variable {k b N p i d D R : ℕ}

lemma kiosk (d D : ℕ) (H : Hol G) : ∃ S : Finset (Snap G d), ∃ a c : ℝ,∃ v : ℕ,0≤a ∧ 0≤c ∧
    (∀ p : poly (KeyIn G d),trim p (LiftMark.key G d) d=p → ∀ B : ℝ, 0≤B → (∀ i∈S, ‖aeval (kp d i) p‖≤B) → coin p≤a*B) ∧
      ∀ i∈ S, ∀ (b : ℕ) (n : Side) (o : Site n) (h : 2*(b+1) < n.val) (p : BudgetPoint) (L : poly (links G o b)), L.totalDegree≤D →
        let T := tacks H h i
        ‖evaluate_ray (walked T L) d‖ ≤ coin L*c*(1+(b:ℝ))^v ∧
          ‖evaluate_ray (walked (snips H h p i) L) d-evaluate_ray (walked T L) d‖≤ coin L*c*(1+(b:ℝ))^v*p.threshold := by
  obtain ⟨X,a,ha,Hx,ht⟩:= molds (KeyIn G d) d 1 zero_lt_one
  choose f hf using fun i : X=> kp_contains i.val
  let Y:= X.attach.image f
  choose A r hc Hc using fun i : Y => shades H i.val d D
  let v:= Finset.univ.sup r
  let c := ∑ j,A j
  refine ⟨Y,a,c,v,ha,Finset.sum_nonneg (fun i _=> hc i),fun p hp B hb he => ht p ?_ B hb ?_,?_⟩
  · apply Finset.sup_le; intro i hi
    have hx : i.sum (fun _ n => n) ≤ Finsupp.weight (LiftMark.key G d) i := by
      rw [Finsupp.weight_apply, Finsupp.sum, Finsupp.sum]; exact Finset.sum_le_sum fun a h=> le_mul_of_one_le_right (Nat.zero_le _) (by dsimp [LiftMark.key, generation]; omega)
    exact hx.trans (spots_output p i (hp.symm ▸ hi))
  · intro j hj; let i:Y:=⟨f ⟨j,hj⟩, Finset.mem_image_of_mem f (Finset.mem_attach ..)⟩
    have ho := he i.val i.property
    change ‖aeval (kp d (f ⟨j,hj⟩)) p‖≤B at ho; rw [hf] at ho; exact ho
  intro i hi b n o h p L H
  let z:Y:=⟨i,hi⟩; obtain ⟨hh,hT⟩ := (Hc z b n o h p).2.2 L H; let u:= 1+(b:ℝ)
  have hy : 0≤coin L := sign _ _ zero_le_one
  have hz : coin L*A z*u^(r z)≤ coin L*c*u^v := mul_le_mul (mul_le_mul_of_nonneg_left (Finset.single_le_sum (fun i _=>hc i) (Finset.mem_univ z)) hy)
    (pow_le_pow_right₀ (show 1≤u by dsimp only [u]; simp) (Finset.le_sup (f:=r) (Finset.mem_univ z))) (pow_nonneg (by unfold u; positivity) _)
    (mul_nonneg hy (Finset.sum_nonneg fun i _=>hc i))
  exact ⟨hh.trans hz,hT.trans (mul_le_mul_of_nonneg_right hz p.threshold_pos.le)⟩

lemma drift (H : C.Makes) (d D : ℕ) (hd : d≤D) : ∃ c : ℝ, ∃ v : ℕ, 0 ≤ c ∧
    ∀ {k N p b R i : ℕ} (S : Rules G) (ht : Provision C d k N p i b) (he : 4*b≤R),
      C.ref d≤k → k≤N → ∀ {β : ℝ},0≤β→ ∀ w L,WRead S k N p d b i D β w L→
          let T:= C.path.rep N p k; let F:=C.labels.level d
          coin (expose F (awake C d k N p w)-trim (unwind (o:=0) ht.length he d L) (LiftMark.key G d) d) ≤
              β * moneys C d k N p w * c * (1+(b:ℝ))^v*(T.p.threshold+expCut T.p i) := by
  obtain ⟨s,a,c,v,ha,hc,Hs,hs⟩ := kiosk d D C.params
  refine ⟨3*c*a,v,by positivity, fun {k N p b R i} S ht he hx hv {β} hb w L hw => ?_⟩
  obtain ⟨P,Q,hl,H₁,H₂⟩:=hw.plans; obtain ⟨eta₁,h₁,hs₁⟩ := H₁; obtain ⟨eta₂,h₂,hs₂⟩:=H₂
  let Y:= C.path.rep N p k;let F:=C.labels.level d
  let X:= expose F (awake C d k N p w); let K:= LiftMark.key G d; let V:= unwind (o:=0) ht.length he d (G:=G); let y (f):=trim (V f) K d
  let T:= X-y L
  have hxv : trim T K d=T := by
    have h1 : trim X K d=X := circle ..
    have h2 : trim (y L) K d=y L := by ext i; unfold y; simp only [trim_coeff]; split_ifs<;>simp
    unfold T; rw [trim_sub,h1,h2]
  intro _ _
  let M:=moneys C d k N p w; let P₀:= 1+(b:ℝ); let J:= c* P₀^v; let X':= expCut Y.p i
  have hM : 0≤M:= money_nn ..; have hJ : 0≤J := mul_nonneg hc (pow_nonneg (by unfold P₀; positivity) _)
  have hX' : 0≤X' := (Real.exp_pos _).le; have ho:= Y.p.threshold_pos
  have hx (A) (h:A∈s) : ‖aeval (kp d A) T‖ ≤ 3*β*M*J*(Y.p.threshold+X') := by
    rw [show T=X-(y P+y Q) by unfold T; rw [hl]; unfold y; rw [map_add,LiftMark.trim_add],map_sub,map_add, sub_add_eq_sub_sub]; apply (norm_sub_le ..).trans
    have he (L) : aeval (kp d A) (y L)= evaluate_ray (walked (tacks (o:= (0:Site (C.side k p))) C.params ht.length A) L) d := by rw [veneer _ ht.length he,ray_stamp]
    rw [he,he, ← show evaluate_ray _ d=aeval (kp d A) X from purchase_pin (C:=C) S H hx hv ht P A hs₁ hd]
    have hh := (hs _ h _ _ _ ht.length Y.p P hs₁.produced.choose_spec.1.degree).2
    have hF := (hs _ h _ _ _ ht.length Y.p Q hs₂.produced.choose_spec.1.degree).1
    have heP : coin P≤ 3*M*β := hs₁.charge.trans (mul_le_mul_of_nonneg_right h₁.2.2 hb)
    have heQ : coin Q≤ X'*M*β := hs₂.charge.trans (mul_le_mul_of_nonneg_right h₂.2.2 hb)
    apply (add_le_add hh hF).trans
    change coin P*c*P₀^_*Y.p.threshold + coin Q*c*P₀^_ ≤ _
    rw [mul_assoc (coin P), mul_assoc (coin Q)]; change _ * J * _ + _*J≤_
    apply (add_le_add (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right heP hJ) ho.le) (mul_le_mul_of_nonneg_right heQ hJ)).trans
    nlinarith only [mul_nonneg (mul_nonneg (mul_nonneg hX' hM) hb) hJ]
  refine (Hs T hxv _ (show 0≤3*β*M*J*(Y.p.threshold+X') by positivity) hx).trans_eq ?_; unfold J; ring

-- threshold/dimension coupons

def scouts (k : ℕ) := Perch.M (clim C.path.levels k)
def sizeQ (k : ℕ) := 8* walls (clim C.path.levels k)
def year (D k : ℕ) := (C.path.levels.params k).columns ≤ bill (shade D/4) (clim C.path.levels k)
-- volume coordinate cost
lemma checks (n : ℕ) (e : ℝ) (t : ℝ) (hg : G.Simple) (ht : 0<t) :
    ∀ᶠ k in atTop,∀ p : ℕ, ((Fintype.card (Up C k p (sizeQ C k)):ℝ)+1)^n * e ≤ bill t (clim C.path.levels k) := by
  let a := (Fintype.card G.ColorIndex:ℝ); let w:ℝ:= (17:ℝ)^4*4*a+1
  have hp : 0≤a := Nat.cast_nonneg _;have hx : 0≤w := by unfold w; positivity
  let K:= C.path.levels; let h:= hat_rate K hg
  filter_upwards [h.eventually (roomier (4*n) ht ((max 0 e)*w^n)),h.eventually (big.eventually_ge_atTop 1)] with k hm hl p
  let i:= sizeQ C k; let s:= clim K k; let b:=walls s; let m:=lengthW s
  have hb : 1≤b := hl; have ht : b≤m:= by dsimp only [m,lengthW,b]; nlinarith only [hb]
  let c:= Fintype.card (Up C k p i)
  let o : Site (C.side k p):= 0
  have he : (i+i+1:ℝ) ≤ 17*(1+(m:ℝ)) := by
    have he : (b:ℝ) ≤ m := by exact_mod_cast ht
    rw [show i=8*b from rfl]; push_cast; linarith only [he,Nat.cast_nonneg (α:=ℝ) b]
  have hf : (c:ℝ) ≤ (((17*(1+(m:ℝ)))^4)*4)*a := by
    have H : c ≤ (i+i+1)^4*4*Fintype.card G.ColorIndex := by
      unfold c Up links; rw [Fintype.card_prod,Fintype.card_coe]; exact Nat.mul_le_mul_right _ (broad o i)
    have hv : (c:ℝ) ≤ ((i:ℝ)+i+1)^4*4*a := by unfold a; exact_mod_cast H
    exact hv.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) he 4) (by norm_num)) hp)
  have hC : (c:ℝ)+1 ≤ w*(1+(m:ℝ))^4 := by
    unfold w; linarith only [hf,one_le_pow₀ (show 1≤ 1+(m:ℝ) by simp) (n:=4)]
  apply le_trans _ hm
  change ((c:ℝ)+1)^n * e ≤ max 0 e*w^n*(1+(m:ℝ))^_
  calc
    _ ≤ (w*(1+(m:ℝ))^4)^n * max 0 e := by
      rw [mul_comm _ e,mul_comm _ (max 0 e)]; exact mul_le_mul (le_max_right ..) (pow_le_pow_left₀ (by positivity) hC n) (by positivity) (le_max_left ..)
    _ = _ := by rw [mul_pow,pow_mul];ring

lemma housing (d : ℕ) (hg : G.Simple) (hc : C.Makes) : ∀ᶠ k in atTop,
    4*sizeQ C k ≤ wood C.path.levels k ∧ ∀ p N (_ : k≤N), Provision C d k N p (scouts C k) (sizeQ C k) := by
  let A:= C.path.levels; let a:= C.localSection d; let L k:=clim A k
  let h:=hat_rate A hg
  have hx : Tendsto (sizeQ C) atTop atTop := by
    -- ≥
    refine tendsto_atTop_mono ?_ ((big).comp h); intro k; change walls (clim A k) ≤ 8*walls (clim A k) ; omega
  have hp (i : Cover) : ∀ᶠ k in atTop,i∈box (sizeQ C k) := by
    filter_upwards [eventually_all.mpr (fun j : Axis=> hx.eventually_ge_atTop ((i j).natAbs))] with k H
    rw [box_test]; constructor<;>intro j <;> specialize H j <;> omega
  filter_upwards [(eventually_all_finite (a.stencil.finite_toSet)).mpr (fun i _=> hp i), h.eventually (big.eventually_ge_atTop 32), h.eventually (zone_power 1 (a:=1) (by norm_num)),
    Wall.far A hg 1 1280] with k hs ht hh hF
  let b:=walls (L k); change 32 ≤ b at ht
  let u:= sizeQ C k
  have hi : u=8*b:= rfl
  have hk : 4* u ≤ wood A k:=by change _≤b^2; rw [hi]; nlinarith only [ht]
  refine ⟨hk, fun p N hn=>?_⟩
  let m := (C.side k p).val
  have he := (div_le_one (by positivity : 0 < (m:ℝ))).mp (hF p)
  rw [pow_one] at hh; have hz : (u:ℝ)≤bill 1 (L k) := (show (u:ℝ)≤ wood A k by
    exact_mod_cast (by omega : u≤wood A k)).trans hh
  have hQ : 10*sizeQ C k<m := by
    suffices ha : 10*(u:ℝ) < m by exact_mod_cast ha
    have hb : 0 < (u:ℝ) := by exact_mod_cast (by omega : 0<u)
    linarith only [he,hz,hb]
  refine ⟨hs,hQ,?_,by change 2*(u+1)<m; change 10*u<m at hQ; omega⟩
  rw [(hc.wilson.represents N p k hn).vac]
  let v:= scouts C k
  change v*(4*v+2)+2*v ≤ 8*v^2
  have ht : 1≤v := A.budget k|>.B_pos
  nlinarith only [ht]

lemma shrank (a : ℝ) (hg : G.Simple) (h : C.Makes) : ∀ᶠ k in atTop,∀ N (_ : k≤N) p,
    expCut (C.path.rep N p k).p (scouts C k) ≤ bill (-a) (clim C.path.levels k) := by
  let A:= C.path.levels; let e:= (A.budget 0).supportExponent; have he : 0<e := (A.budget 0).exponent_pos
  let P:= (max 1 a)
  have hP : 0 < P := zero_lt_one.trans_le (le_max_left ..)
  filter_upwards [(hat_rate A hg).eventually ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2 |>.comp y_rate).eventually (ge_mem_nhds (div_pos he hP))),
    (Real.tendsto_log_atTop.comp (hat_rate A hg)).eventually_ge_atTop 1] with k hv hx N hn p
  let s:=clim A k; let V:=(A.budget k);let c:= V.supportExponent
  rw [(h.wilson.represents N p k hn).vac]; unfold expCut bill; apply Real.exp_le_exp.mpr
  change y s ^2*Real.exp (-y s)≤ e/P at hv; change 1 ≤ Real.log s at hx
  let i:=scouts C k
  have hh : Real.exp (y s) ≤ (i:ℝ) := by
    rw [y,Real.exp_log (by linarith)]; exact le_trans (by nlinarith only [hx]) (Nat.le_ceil ((Real.log s)^2))
  rw [Real.exp_neg,← div_eq_mul_inv, div_le_div_iff₀ (Real.exp_pos _) hP] at hv
  have hc : e ≤ c := A.fits.deepExp (Nat.zero_le _)
  apply le_trans _ (mul_le_mul_of_nonneg_left (neg_le_neg (show a≤P from le_max_right ..)) (boil_pos s)); change -c*i ≤ (y s)^2*(-P)
  linarith only [hv,mul_le_mul hc hh (Real.exp_pos _).le (he.le.trans hc)]

def shadow (k n D : ℕ) (c : ℝ) := ((Fintype.card (Up C k n (sizeQ C k)):ℝ)+1)^D*c

def furnace (L : C.label d →ₗ[ℂ] poly (Up C k p (sizeQ C k))) (r : 4*sizeQ C k≤ wood C.path.levels k)
    (ℋ : Provision C d k N p (scouts C k) (sizeQ C k)) := gram L ℋ.length r (shrink C k N p)

lemma setter (a : ℝ) (ha : 0<a) (M : ℝ) (g : G.Simple) (h : C.Makes) (j : ℕ) : ∀ᶠ k in atTop,M*(1+(sizeQ C k:ℝ))^j ≤ bill a (clim C.path.levels k) := by
  filter_upwards [(hat_rate C.path.levels g).eventually (roomier j ha (max M 0)),housing C 0 g h] with k hf hl
  let A:= C.path.levels; have ht : sizeQ C k ≤ lengthW (clim A k) := by have hh : 4*sizeQ C k ≤ lengthW (clim A k):= hl.1; omega
  refine le_trans ?_ hf
  exact mul_le_mul (le_max_left _ _) (pow_le_pow_left₀ (by positivity) (add_le_add_right (Nat.cast_le.mpr ht) (1:ℝ)) j)
    (by positivity : 0≤(1+(sizeQ C k:ℝ))^j) (le_max_right ..)
private lemma billed_wide (a : ℝ) (ha : 0<a) (g : G.Simple) (h : C.Makes) (j : ℕ) : ∀ᶠ k in atTop,(1+4*(sizeQ C k:ℝ))^j ≤ bill a (clim C.path.levels k) := by
  filter_upwards [setter C a ha (4^j) g h j] with k hk; apply le_trans _ hk
  rw [← mul_pow]; apply pow_le_pow_left₀ (by positivity); linarith only

private lemma trend_diet (a : ℝ) (ha : 0<a) (d : ℕ) (g : G.Simple) : ∀ᶠ k in atTop,Diet (faceTest C d k) 0 (bill a (clim C.path.levels k)) := by
  obtain ⟨c,hc,h⟩ := Glimmer.display (G:=G) (d:=d)
  filter_upwards [(hat_rate C.path.levels g).eventually (roomier d ha c)] with k ht x
  let T:= wood C.path.levels k; let I:= x.val
  have he := Real.exp_pos (boil (clim C.path.levels k)*a)
  refine ⟨?_,by simp only [Pi.zero_apply,coin, Rise.pay_nothing]; exact he.le,fun _ hs=>False.elim (by simp at hs)⟩
  rw [LiftMark.first,exchange_x,faceTest,LiftMark.ink,glyph,map_sum]
  apply (Rise.collect _ zero_le_one ..).trans
  apply le_trans _ ((h T I ((tracing ..).1 x.property)).trans ht)
  apply Finset.sum_le_sum; intro i _; rw [Finsupp.linearCombination_single]
  apply (retiring _ _).trans; rw [Complex.norm_real]; simp only [coin,Rise.pay_X,one_pow,mul_one]; exact le_rfl

-- uniform at Era beyond YEAR demand
lemma prototype (c : ℝ) (hc : 0≤c) (d D : ℕ) (S : Rules G) (g : G.Simple) (h : C.Makes) (hd : d≤D) : ∀ᶠ k : ℕ in atTop,
    C.ref d ≤ k→ year C D k → ∀ p N : ℕ,k≤N →
      let n:= sizeQ C k; let m:=scouts C k;let s:=clim C.path.levels k; let b:= tin s D
      ∀ (ι : Provision C d k N p m n) (r : 4*n≤wood C.path.levels k) (L : C.label d →ₗ[ℂ] poly (Up C k p n)) (W : AtlasData G C.S p), Stamped n (wood C.path.levels k) k W r →
        (∀ v,WRead S k N p d n m D (shadow C k p D c) v (L v)) →
          MarkedStart (furnace C L r ι) (control (k:=k) W 0 _) D b (GaugeScale C k N p) (bill (-1) s) N p := by
  obtain ⟨K,v,hK,HK⟩:= drift C h d D hd
  have hh:= shade_pos D; have hy := shaded D; let β:=shade D/4
  let A:= C.path.levels; let ha:= hat_rate A g
  have he : 0<β := by dsimp only [β]; positivity
  have h₁ : β+β+β<shade D := by dsimp only [β];linarith only [hh]
  have h₂ : β+β+β+-4<(-1:ℝ) := by linarith only [h₁,hy]
  filter_upwards [ setter C β he K g h v,billed_wide C β he g h D, checks C D c β g he,
    booth A 4 g, shrank C 4 g h,ha.eventually (transports h₁ 4),ha.eventually (transports h₂ 2), trend_diet C (shade D) hh d g] with k ha hb hz ht hp hg hQ hX i H p N hN n m s b ι r L W hS hL
  let M := furnace C L r ι; let K':= control (k:=k) W 0 (wood A k); let B:= shadow C k p D c
  let F:= C.labels.level d; let Y:=C.path.rep N p k; let τ:= Y.p.threshold
  let g0:= GaugeScale C k N p; let X:= shrink C k N p
  have hv:= shrink_pos C h hN p
  have hC : c≥0:=hc; have hx : B≥0 := by dsimp only [B,shadow];positivity
  have hB : τ= A.clock.threshold k := by rw [show τ=Y.p.threshold from rfl, show Y.p= A.budget k from (h.wilson.represents N p k hN).vac];rfl
  have he : τ/g0=X⁻¹ := by rw [hB,show X=g0/(A.clock.threshold k) from rfl,inv_div]
  let α := bill β s; have hT : 0≤α := (Real.exp_pos _).le
  have hu (w): moneys C d k N p w ≤ α*F.coeffSize (awake C d k N p w) := mul_le_mul_of_nonneg_right H (paid_pos C ..)
  have hy : B≤α := hz p
  let C0:= faceTest C d k
  have h' (w) : factors (↑(τ/g0):ℂ) (M w)=rename (calls r) (dustAt ι.length (L w)) := by
    dsimp only [M,furnace]; rw [noteL,he]; unfold luminosity
    change factors (↑(X⁻¹):ℂ) (rename _ (factors (↑X:ℂ) _))=_
    rw [Normal.labelled,sprinkle,Complex.ofReal_inv,factors,factors,cycles _ (↑X:ℂ) (by exact_mod_cast (show X≠0 from hv.ne'))]
  refine ⟨?_,fun w=>⟨lit_power L ι.length r X w|>.trans (tallied (hL w) hx).1,?_⟩,caressed W L ι.length r X hS h i hN hx hL,⟨0,hX,fun w=>?_⟩⟩
  · unfold furnace; rw [noteL]; unfold luminosity; rw [show L (C.refUnit d) = _ from sterling h i hN hx hL]; exact (by simp [dustAt])
  · change coin (factors (↑(A.clock.threshold k/g0):ℂ) (M w))≤b* _
    rw [← hB,h',Normal.labelled]
    let J:= dustAt ι.length (L w); let J':= F.coeffSize (awake C d k N p w)
    have hh:= Rise.rise (fun z : slotC G n=> Finsupp.single (calls r z) 1) 0 (show (0:ℝ)≤1 from zero_le_one) (c:=1) le_rfl ?_ J le_rfl
    rotate_left
    · intro s; simp
    have hD : coin J≤ coin (L w) * (1+4*(n:ℝ))^D := by
      refine Rise.rise _ _ zero_le_one (by simp) ?_ _ (tallied (hL _) hx).1
      intro i; have he := prices (word G ι.length i.1) i.2
      have hz : (↑(word G ι.length i.1 |>.length):ℝ) ≤ 4*n := by exact_mod_cast lengths_word G ι.length i.1
      exact he.trans (hz.trans (le_add_of_nonneg_left zero_le_one))
    have hm : 0≤ J':=paid_pos C ..
    rw [one_pow,mul_one] at hh; apply hh.trans (hD.trans ?_)
    have hk : 4*α*α*α≤b := by
      have hs : 4* Perch.bill (β+β+β) s ≤ b:=hg; simp_rw [← Perch.overlap] at hs; linarith only [hs]
    have hp : coin (L w)≤(4*(α*J')*α) := (tallied (hL w) hx).2.trans (mul_le_mul (mul_le_mul_of_nonneg_left (hu w) (by norm_num)) hy hx (by positivity))
    apply (mul_le_mul hp hb (pow_nonneg (by positivity) _) (by positivity)).trans; linarith only [mul_le_mul_of_nonneg_right hk hm]
  · let T:= factors (↑(τ/g0):ℂ) (M w)
    have ho' : garnish 0 C0 τ=exchange C0 := by ext1 i; rw [zips _ _ _ τ (by exact Y.p.threshold_pos)]; simp [LiftMark.first]
    suffices h : coin (Tariffs.expose F (awake C d k N p w)-trim (garnish 0 C0 τ T) (LiftMark.key G d) d) ≤ paid C d k N p w * Perch.bill (-1) s by simpa only [T,hB] using! h
    unfold T; rw [h',ho']; apply (HK _ ι r i hN hx _ _ (hL w)).trans
    let y := Perch.bill (-4) s
    have hy' : τ+expCut Y.p m≤ y+y:= add_le_add (show τ ≤ y from hB ▸ ht) (hp N hN p)
    have hx' : 0≤ τ+expCut Y.p m := add_nonneg Y.p.threshold_pos.le (Real.exp_pos _).le
    let P:= paid C d k N p w; have hn : 0≤P := paid_pos C ..
    have H : B*moneys C d k N p w * K * (1+(n:ℝ))^v ≤ α*(α*P)*α := by
      rw [mul_assoc (B*_)]; exact mul_le_mul (mul_le_mul hy (hu w) (money_nn C ..) hT) ha (mul_nonneg hK (by positivity)) (by positivity)
    apply (mul_le_mul H hy' hx' (by positivity)).trans
    have hv : 2*(α*α*α*y) ≤ bill (-1) s := by dsimp only [α,y]; simp_rw [overlap]; exact hQ
    linarith only [mul_le_mul_of_nonneg_right hv hn]
end YM.Next.Rank.Spindle
