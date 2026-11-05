import YM.MergeProof.East.Eupho
import YM.TraceExtension.Prom.Orion.Ducat
set_option autoImplicit false
set_option maxHeartbeats 480000
noncomputable section
namespace YM.Next.Rank.East
open Function Filter RG Labels Source Thirst Baler Lattice Wilson MeasureTheory Corona Value Glyph Marker Perch Vac.Numbers Alarm Station Cells Spindle Atlas Edition Normal LiftMark Rise MvPolynomial Configuration Ribbon Price
open Extra.Histories Motion PhysicalNext PhysicalNext.RankCovariance
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}{n:Side}{b D k i N p d q:ℕ} {C:Family G} {t a g δ e:ℝ}
def InvoiceSky (C:Family G)(k N p d:ℕ)(U:Module.End ℂ (C.label d)) : Prop:= ∀ x,
   let z:= awake C d k N p x;let f:= C.labels.level d
   f.coeffSize (z-U x) ≤ Perch.bill (-1/2) (clim C.path.levels k) * f.coeffSize z

private lemma conserveSky {E:Type*}[AddCommGroup E][Module ℂ E](v:E): (quota:ℂ) • (∑ _ : Signed,v) = v:=by
    simp only [Finset.sum_const,Finset.card_univ,quota, Complex.ofReal_inv, Complex.ofReal_natCast, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]; rw [inv_mul_cancel₀ (by exact_mod_cast (show Fintype.card Signed≠0 from Fintype.card_pos.ne')),one_smul]
private lemma conserveR_sky (v:ℝ):quota*(∑ _ : Signed,v)= v:=by unfold quota;simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; rw [inv_mul_cancel_left₀ (Nat.cast_ne_zero.mpr Fintype.card_pos.ne')]
lemma mintingSky (B:Binding C) (hG:G.Simple)(h:C.Makes)(H: ParadeX C) (d D:ℕ)(hd : d ≤ D):
    ∀ᶠ k in atTop, C.ref d≤ k → year C D k → D+1 ≤ (C.path.levels.params k).order → ∀ N p, k≤N → ∀ (Q : Rep G (C.side k p)) (q : ℕ),
      Q.p.threshold= Spindle.tau C.path.levels k→Q.p.B=walls (clim C.path.levels k) → 8 ≤ q →
       let K:=RankCovariance.stamp C.path.levels N p
       Hail C k p D K→ ∃ Y:StampDuty C k N p d D Q q K, (∀ s x,Y.T (mir (C.labels.level d) s x)=mir (C.labels.level d) s (Y.T x)) ∧ InvoiceSky C k N p d Y.T :=by
    let f:= C.labels.level d;let a:= orbitCost f;let b:=(2*a*a)⁻¹
    have hA:1≤a:=orbitCost_one_le _; have ha:0<a:=zero_lt_one.trans_le hA
    have hb:0<b:= inv_pos.mpr (by positivity); have hC: b*a*a = 1/2:=by unfold b; field_simp
    have hv: b*a≤1:= (le_mul_of_one_le_right (mul_nonneg hb.le ha.le) hA).trans (by rw [hC];norm_num)
    obtain ⟨R⟩:= charts G; obtain ⟨c,hc,hV⟩:= machine R D C h d
    filter_upwards [housing C d hG h,kpc_plusSky D C hG h d b hb ((le_mul_of_one_le_right hb.le hA).trans hv),prototype C c hc d D R hG h hd,LiftMark.supports D C hG h,ahead R h hG H c hc d D b hb,
       (hat_rate C.path.levels hG).eventually (transports' (show shade D < 1 from lt_of_le_of_lt (shaded D) (by norm_num)) 1 hb)] with k hp hf hx ht hh hz hr he hw N p hN Q q h1 h2 h3 K hX
    have u:= hp.2 p N hN; let i:=scouts C k;let V:=C.path.rep N p k
    have hl: V.p=C.path.levels.budget k:=(h.wilson.represents N p k hN).vac
    obtain ⟨P,hP⟩:=hV k (sizeQ C k) p i N hr hN (hl ▸ hw)
    let r:=hp.1;let L:=furnace C P r u
    let W: C.label d→ₗ[ℂ] poly (slotC G (sizeQ C k)):= (LiftMark.factors ((↑(GaugeScale C k N p/V.p.threshold)):ℂ)).toLinearMap.comp ((exchange (Spindle.visit (G:=G) (o:=0) u.length)).toLinearMap.comp P)
    have hl'(x): raww C k N p d u.length P x=W x:= rfl
    let D':=control K (k:=k) 0 (wood C.path.levels k)
    let S:=clim C.path.levels k
    have hM:= hx hr he p N hN u hp.1 P K (hX.1 hp.1) hP
    obtain ⟨T,hT⟩:= hf N p hN K L hX.2 hM
    have hE' : 0≤ shadow C k p D c:=by unfold shadow; positivity
    have hg(x): L x=rename (calls r) (W x):=carried h hN r u («F»:=P) x
    let ω':= paid C d k N p
    have hY(x): coin (W x) ≤ b*Perch.bill 1 S*ω' x:=by
       obtain ⟨hv,hB,hD⟩:= ht N hN p
       apply (coin_rename (W x) (calls r) (call_inj r)).trans; rw [← hg]
       apply (blends (L x) _ (show 1 ≤ C.path.levels.clock.threshold k / GaugeScale C k N p from (le_div_iff₀ hv).mpr (by simpa))).trans ((hM.2.1 x).2.trans ?_)
       rw [one_mul] at hz; exact mul_le_mul_of_nonneg_right hz (paid_pos ..)
    let m:=Perch.bill (-1/2) S; have hm:0 < m:=Real.exp_pos _
    have hl : m ≤ 1:= (Glimmer.billed S (by norm_num : (-1/2:ℝ) ≤ 0)).trans (by simp [Perch.bill])
    have hppa: b*m*a*a ≤ 1:= by linarith only [show b*m*a*a = 1/2*m from by rw [← hC];ring,hl]
    have hp(s:Signed):∃ Y: StampDuty C k N p d D Q q K,Y.T=emblaze f s T:= by
       let U:= (exchange (pivot s)).toLinearMap.comp (W.comp (mir f s⁻¹));let R:= Wick K ((rename (calls r)).toLinearMap.comp U);let D0:=emblaze f s T
       let x(v):=mir f s⁻¹ v
       have hF(v): Spirit (U v):= wreath s _ (framed h hr hN u hE' hP (x v))
       have hV(v): ω' (x v) ≤ a*ω' v:=by change f.coeffSize (Price.awake C d k N p (mir f s⁻¹ v))≤_; rw [show (Price.awake C d k N p (mir f s⁻¹ v))= _ from (H d k hr N p hN s⁻¹ v).1];exact pirouette ..
       refine ⟨⟨r,U,hF, fun x=> (Rise.ascent _ _).trans (qualified u hE' hP _),fun v=> ?_,R,fun v=>rfl,D0,labelledT (mul_pos hb hm) hppa W (Wick K L) r T hT (fun v=> by change milk _ (L v)=_; rw [hg]) H hr hN B s,fun v=>?_⟩,rfl⟩
       · let m:=Perch.bill 1 S; have hb':0< m:=Real.exp_pos _; apply (cheaper s (W (x v))).trans ((hY _).trans ?_); apply (mul_le_mul_of_nonneg_left (hV v) (by positivity : 0≤ b*m)).trans; linarith only [mul_le_mul_of_nonneg_right hv (mul_nonneg hb'.le (paid_pos C d k N p v))]
       let Y:=halo (q*Q.p.B) ({0}:Support (C.side k p)); let Y0:= Spindle.patch (n:=C.side k p) (sizeQ C k) 0
       have he': Y0 ⊆ Y:= by unfold Y0 Spindle.patch Y; apply halo_mono _ le_rfl; unfold sizeQ; rw [h2]; gcongr
       have hB:=origin0 (U v) (hF v) (GaugeScale C k N p) (n:=C.side k p) 0
       refine ⟨⟨fun i=> (Provision.contained (h:=h) (hk:=hr) (hN:=hN) u v i).trans he'⟩,⟨hB.inv,hB.meas,fun U V h=> hB.locally _ _ (agrees_mono h (fun _ hx=> he' hx))⟩,fun Z h'=>?_⟩
       have hp:= hh hr he N p hN u s (x v) P hP (required h hN r u D' hM (ht N hN p|>.2.1) (x v)) Z (h1 ▸ Disjoint.mono_left he' h')
       rw [show (C.labels.level d).act s.ortho (x v)=v from undone f s v] at hp
       apply hp.trans; let m:=Perch.bill (-(D:ℝ)) S; have hV':0< m:=Real.exp_pos _
       apply (mul_le_mul_of_nonneg_left (add_le_add_left (hV v) (ω' v)) (by positivity : 0≤b*m)).trans
       have he0: b*a≤1/2:= (le_mul_of_one_le_right (mul_nonneg hb.le ha.le) hA).trans_eq hC
       have he1: b≤1/2:= (le_mul_of_one_le_right hb.le hA).trans he0
       change b*m*(a* _+ω' v) ≤ m*ω' v; have ht:=paid_pos C d k N p v;change 0≤ω' v at ht; linarith only [mul_le_mul_of_nonneg_right he0 (mul_nonneg hV'.le ht),mul_le_mul_of_nonneg_right he1 (mul_nonneg hV'.le ht)]
    choose Y hy using hp
    obtain ⟨w,hw⟩:= ruled Y
    refine ⟨w,(fun s x=> by rw [hw];exact lawOf Y T hy s x),fun x=>?_⟩
    let z:= awake C d k N p x
    let Z := blendT Y
    have he(s:Signed): f.coeffSize (z-(Y s).T x) ≤ m*f.coeffSize z:= by
       rw [hy s]; let v:= mir f s⁻¹ x; let y:= awake C d k N p v
       have hj : mir f s y=z:=by unfold y v mir;rw [(H d k hr N p hN s⁻¹ _).1];exact undone ..
       have hk:f.coeffSize y ≤ a*f.coeffSize z:=by
          unfold y v mir; rw [(H d k hr N p hN s⁻¹ _).1]; exact pirouette ..
       change f.coeffSize (z-mir f s (T v)) ≤ _; rw [show _=mir f s (y-T v) from (by rw [map_sub,hj]: z-mir f s (T v)=_)]
       have hp : f.coeffSize (y-T v) ≤ b*m*(a*f.coeffSize z)/2:= (hT.credit v).trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hk (mul_pos hb hm).le) (by norm_num))
       apply (le_trans ((pirouette ..).trans (mul_le_mul_of_nonneg_left hp ha.le)))
       change a*_ ≤ _; rw [show a*(b*m*(a*f.coeffSize z)/2)=(b*a*a)*m*f.coeffSize z/2 by ring,hC];
       have hE:0≤ f.coeffSize z:=paid_pos C d k N p x
       linarith only [mul_nonneg hm.le hE]
    change f.coeffSize (z-w.T x) ≤ m*f.coeffSize z; rw [hw,blendT,LinearMap.smul_apply,LinearMap.sum_apply,show z - (quota:ℂ) • ∑ i,(Y i).T x=(quota:ℂ) • (∑ i,(z-(Y i).T x)) by rw [Finset.sum_sub_distrib,smul_sub,conserveSky]]
    rw [Size.smul,Complex.norm_real,Real.norm_of_nonneg quota_pos.le]; exact (mul_le_mul_of_nonneg_left ((Size.finite ..).trans (Finset.sum_le_sum fun i _=> he i)) quota_pos.le).trans_eq (conserveR_sky _)
end YM.Next.Rank.East
