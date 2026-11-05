import YM.RG08.Creek.Palm
/-! # Gathering $pgeo.Exp$ before launching soft continuation. Derived with no independent-coefficient substitution. -/
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.RG08.Creek
open Function Finset Filter RG Lattice Laurent Quire Vale Bloch Next.Free Stationary Shade Wax Town Bands Plot Needle Tall Scores Push.AbsoluteSums Work.F08 Door Analysis Harvest
open Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset RG Bloch Conductor Staffer Reflect UVExt.Paths Planned.PrimaryIntegral295 Place Source Source.Drops Labels Summit Wings High Pill Taste Run Matrix PowerSeries
open scoped Topology ContDiff BigOperators Real Classical Matrix
variable {X:Chain} {G:Gauge}{E e r d τ D j t f i k m n :ℕ}{R θ C C' w:ℝ}{F:Labels.Frame G d}{Ω:SectionData F}{ν:G.ColorIndex}{D':ChartRatio G}{H:Hol G}
variable {P:KPrices X.kernel}{g:KGate P}{Q:Lending G X.kernel}{S:Prism G X.kernel g Q E}
variable {h:1/2≤R}{hD:d+1 ≤ D}{T:Signals P Q E τ H Ω h hD}
variable {I J Y:Type} [Fintype I][DecidableEq I]{u:Y→Windows}{a b:I→ℕ}{Z:ℕ→ℝ}{p:J→ Dial u}
variable {W:J→ℕ}{U:J→ I→ ℕ→ BoardU D R G} -- del
section shapes
structure GatesC (X:Chain)(p:J→Dial u)(W:J→ℕ)(w:J→ℝ):Prop where
    optic : ∀ j, Optic (p j) (W j)
    audience: Audience w
    mass : Weighed w (fun i=> Dial.fee X (p i))
    future : Weighed w (fun i=> priorZ X (p i) (W i))
structure ArcsU (X:Chain)(p:J→Dial u)(W:J→ℕ)(φ:I→J→ Profile D)(C R:ℝ)(T A:I→ J→ℝ) (ρ:J→ℝ):Prop where -- T unused
    life : 0≤ C
    calibration i : 0 ≤ A i
    reads i z: Reads (φ i z).val (A i z)
    space i j : Spatial (φ i j).val (spanP X (p j).K (W j)*C)
    reachable (i:J)(x:E4)(y:I→Cover): y ∈ cope X (p i).K (p i).K (fun j=>φ j i) x R → rural X.S (ρ i) (p i).K (p i).K y univ
variable {ρ w :J→ℝ}{A H':I→ J→ℝ}{p':List I}
local notation "☉" => joinerP
-- Type before all heights/fur. Predictor model Y when known supplies via Master.
lemma house_roll (X: Chain)(p:Dial u)(i:ℕ)(hp:Optic p i): spanP X p.K i= Real.exp (priorZ X p i)∧ 1≤ spanP X p.K i:= by
   have hu: spanP X p.K i=gain X.S 1 p.K i:= by rw [gain_spacing, Real.rpow_one]; rfl
   rw [hu,gain]; simp only [neg_mul,one_mul, neg_sub]; refine ⟨rfl,Real.one_le_exp (by apply sub_nonneg.mpr; exact age_scale_mono X.S hp.2)⟩
theorem spritz_exp (hc:Tights T S ν D' u) (hh: Attract ν D' X p U a b)(hw:BrookW T u I Z)(hb:Bureau Z E X U p A)(hZ:∀ i,vanes a i+E≤τ)(hA:∀ i,0≤ A i)(hp:GatesC X p W w) (q:List I)(hv:q.Nodup)(hP:q.toFinset=univ)(R':ℝ) (h0:0≤ R') :
   ∃ (C:ℝ)(p'':ℕ),0 ≤ C∧ ∀ (ρ:J→ℝ), (∀ i,C*(Dial.fee X (p i))^p'' ≤ ρ i) → ∃ H:J→ℝ, Weighed w H ∧ ∀ (φ:I→J→Profile D) (B:I→J→ℝ), ArcsU X p W φ R' R A B ρ → (∀ i, Via G (vanes a univ) (fpulse X ν D' p W U q a b φ i)) → ∀ (i:J)(e:ℕ), e≤ E→ ∀ r:ℕ, Quire.Lit (spritz X ν D' p W U q a b φ h i e r) (Z (X.J (W i))) (Real.exp (H i)*∏ j, (B j i*A j i)):=by
    -- issue: power_close H depends on rho because hA Arrival term. derive choosing uniform by reindex to all choices (not continuum per-window varying). can relax forall ∃ H. adjust statements.
    obtain ⟨M,K,l,hK,hM,hMK,HL⟩:= high_tail hc hh hw hb hZ hA
    refine ⟨K,l,hK.le,fun ρ hS=>?_⟩ -- adjust
    let V:= joinerP ν D' X p U a b ρ; have hY: Arrival V X p W a w:= ⟨fun i=>(hp.optic _).1,fun i=>(hp.optic _).2, fun i=>riftStyle (owned_tv hh (fun i=> seasonal hc i.appr) h (Harvest.beacon p i)).1 (rule_w ..),hp.audience,hp.mass,hp.future⟩
    let H' i:= M (Harvest.beacon p i); have hz i:H' i ≤ Real.exp (H' i):= (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp _)
    have he i: Fest (Z (X.J (p i|>.K))) E 1 (boon (Real.exp (H' i)) (fun a=> A a i)) (V i) := by
       let u:=Harvest.beacon p i; have hQ:boon (H' i) (fun k=>A k i)≤boon (Real.exp (H' i)) (fun k=>A k i):= fun t=>mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (zero_le_one.trans (hMK _)) (hz i) _) (prod_nonneg fun i' _=> hA _ _)
       have hv := ch_fest (HL u 0 (ρ i) le_rfl (by simpa only [add_zero,mul_one] using hS i)) (boon_pos (fun j=> A j i) (fun s=>hA _ _) _ (zero_le_one.trans (hMK u))) le_rfl
       exact fun t ht j s=> owns_mono (hv t ht j s) le_rfl (mul_le_mul_of_nonneg_left (hQ s) zero_le_one)
    obtain ⟨B,hB,ht⟩:=power_close hY hc hw hZ he hA (hp.mass.sway hp.audience (hM.transfer (Harvest.beacon p))) b
    let K':=ketCost I R' R E τ; have hx:0≤K':=ket_z ..
    let P i:=priorZ X (p i) (W i); let V' i:=(Z (X.J (W i)))
    let W' i:= P i*(4*Fintype.card I:ℕ)+K'+((P i*D+B i)*(Fintype.card I))
    refine ⟨W', (((hp.future.times (Weighed.constant _ (Nat.cast_nonneg _))).plus (Weighed.constant _ hx) hp.audience).plus (((hp.future.times (Weighed.constant _ (Nat.cast_nonneg _))).plus hB hp.audience).times (Weighed.constant _ (Nat.cast_nonneg _))) hp.audience),fun φ b' hφ hL i e hE r=>?_⟩
    let K : SoftP p W 0:=⟨i,W i,le_refl _,(hp.optic _).2⟩; let D'':= vitalK ν D' X p V a b i (W i); let C (k:I):= b' k i; let S:=(V' i); have hs:0 < S:= hw.irrigate _; let H:= (p i).K; let v:=spanP X H (W i); let fi j:= φ j i
    refine rip_mat (hL i) (fun x=> ?_) h
    have hV' z: sang X D'' b fi (p i).K (W i) z=waveProduct X ν D' (p i).K (p i).N z q a b fi (U i) (W i):= broadened q hv hP hh h hc.hv hc.hz fi z ρ i (W i) (hp.optic i).2 (hφ.reachable i z)
    change Quire.Lit (waveProduct _ _ _ _ _ (v • x.val) _ _ _ fi (U i) (W i) e r) S _; rw [← hV']
    have hQ : S≤1:= by
       calc S ≤ secretT T I (X.J (W i)):=hw.prior _
            _ ≤ T.wi (X.J (W i)) := (le_mul_of_one_le_left (secret_t T I _|>.le) (by norm_num : (1:ℝ)≤2)).trans (secret_l ..)
            _≤1:= ((tick_t T _).1.trans (tick_t T _).2).trans (min_le_right ..)
    have ha: v=Real.exp (P i):= house_roll _ _ _ (hp.optic i)|>.1
    let Q':= A; have hz' := ket_s (U:=C) (r:=r) (b:=b) (w:=S) x X D'' fi (B':=fun j=> A j K.i) (fun j=>hφ.calibration _ _) (fun k=> hA _ _) (serves_v hY hc K) hZ h0 (fun s=>hφ.reads s i) (fun k=> hφ.space k i) hs.le hQ (Real.exp_pos _|>.le) (house_roll _ _ _ (hp.optic i)|>.2) (ht K) hE
    apply Ink.raise hz'
    let z:= (Fintype.card I); let r:= ∏ j,b' j i*A j i; let g:=Real.exp
    change v^(4*z)*K' *((v^D * Real.exp (B i))^ (card (univ:Finset I)) * r) ≤ Real.exp (W' i)* r
    rw [Finset.card_univ, ← mul_assoc _ _ r]; apply mul_le_mul_of_nonneg_right _ (prod_nonneg fun j _=>mul_nonneg (hφ.calibration _ _) (hA _ _))
    unfold W'; apply le_trans (b:=v^(4*z)*Real.exp K'*((v^D * Real.exp (B i))^z)); swap; · rw [ha]; simp_rw [← Real.exp_nat_mul, ← Real.exp_add]; rw [← Real.exp_nat_mul,← Real.exp_add]; exact le_of_eq (by congr 1; unfold z; push_cast; ring)
    apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ((le_add_of_nonneg_right (show (0:ℝ)≤1 by norm_num)).trans (Real.add_one_le_exp K')) (pow_nonneg (spanP_pos ..|>.le) _)) (pow_nonneg (mul_nonneg (pow_nonneg (spanP_pos ..|>.le) _) (Real.exp_pos _|>.le)) _)
end shapes
end YM.RG08.Creek
