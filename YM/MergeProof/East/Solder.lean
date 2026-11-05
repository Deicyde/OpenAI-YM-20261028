import YM.MergeProof.East.Canes
import YM.MergeProof.East.Glue
import YM.MergeProof.East.Lava
import YM.MergeProof.East.Trak
import YM.Next.RANK.Odometer

/-!
# Pay the rotated test on W,ν origin & real phase
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.East
open Function Filter RG Labels Source Source.Drops Thirst Baler Lattice Wilson MeasureTheory Corona Value Glyph Marker Perch Vac.Numbers Alarm Station Cells Spindle Atlas Edition Normal LiftMark Rise MvPolynomial Configuration Glimmer Ribbon
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}{n:Side}{b J k i N p d:ℕ} {C:Family G} {t a g δ e:ℝ} {S:Rules G}
-- ahead
lemma wide_fare {v:C.label d}{P:poly (Up C k p b)} (he: WRead S k N p d b i J e v P) (u: Config G (C.side k p))(hu : flags (C.path.rep N p k).p.threshold u=∅):
    ‖wideHol C v i k N p u‖ ≤ expCut (C.path.rep N p k).p i * moneys C d k N p v := by
    obtain ⟨_,_,_,_,e,hv,hs⟩:= he.plans; let E:= wideW C v i k N p
    let Z j:= E j*wideA C v i k N p j u
    have ht (j : wideIndex C v i k N p) : ‖Z j‖ ≤ ‖E j‖*e j := by
      unfold Z; rw [norm_mul]; exact mul_le_mul_of_nonneg_left ((hs.contact j).2 _ (by unfold Healthy; rw [hu]; simp) [] (Nat.zero_le _) (by simp)) (norm_nonneg _)
    have hE := hs.collects.of_nonneg_of_le (fun i=> norm_nonneg (Z i)) ht
    change ‖∑' i,Z i‖≤_; exact (norm_tsum_le_tsum_norm hE).trans ((hE.tsum_le_tsum ht hs.collects).trans hv.2.2)
lemma ahead (S:Rules G)(h:C.Makes)(g:G.Simple)(hw:ParadeX C)(o:ℝ)(hp:0≤o)(d J:ℕ)(κ:ℝ)(hκ:0<κ): ∀ᶠ k:ℕ in atTop,
    C.ref d≤ k → year C J k → ∀ N p,k≤N → ∀ (u:Provision C d k N p (scouts C k) (sizeQ C k))(s:Signed),
     let b:=sizeQ C k;let ε:=tau C.path.levels k;let ε':= (C.path.rep N p k).p;let F:=C.labels.level d;let η:=GaugeScale C k N p;let L:=clim C.path.levels k
     ∀ (x:C.label d) (P : C.label d→ₗ[ℂ] poly (Up C k p b)),(∀ i:C.label d,WRead S k N p d b (scouts C k) J (shadow C k p J o) i (P i)) → coin (raww C k N p d u.length P x) ≤ Perch.bill 1 L*paid C d k N p x → ∀ U:Config G (C.side k p),
      Healthy ε (Spindle.patch b 0) U →
      ‖nearHol C (F.act s.ortho x) (scouts C k) k N p U - signet 0 η (exchange (pivot s) (raww C k N p d u.length P x)) U‖ ≤ κ*Perch.bill (-J) L*(paid C d k N p x+paid C d k N p (F.act s.ortho x)):=by
    let a:=κ/4; have ha:0<a:=by positivity
    let A:=C.path.levels
    let z:ℝ:= -(J:ℝ)-3;let cκ:=α₀ J
    have hz : z+cκ < -(J:ℝ):=by unfold z cκ α₀; have hs:=shaded J;linarith only [hs]
    filter_upwards [chas_v S C o hp d J g h a ha,pole_coal J z C g h,iced S C g h 1,shrank C (-z) g h,checks C J o cκ g (alpha_pos J),
       (hat_rate A g).eventually (transports' hz 1 ha), (hat_rate A g).eventually (transports' (show 1+z< -(J:ℝ) from by unfold z; linarith only) 1 ha)]
      with k h1 h2 h3 h4 h5 h6 h7 hr hW N p hN u s
    intro b ε F η L x P hP hp' U H;let V:=(C.path.rep N p k).p
    let q:= F.act s.ortho x;let i:= scouts C k;let α:=κ*Perch.bill (-(J:ℝ)) L
    let Wx:= raww C k N p d u.length P x
    have hE : 0≤ shadow C k p J o:= by unfold shadow; positivity
    have hc:= origin0 (exchange (pivot s) Wx) (wreath s Wx (framed h hr hN u hE hP x)) η (0:Site (C.side k p)); have hf:= origin0 Wx (framed h hr hN u hE hP x) η (0:Site (C.side k p))
    have he(x:C.label d): Reliable V.threshold G (C.side k p) (Spindle.patch b 0) (nearHol C x i k N p):= (Edition.reads_glance x h hr hN p i ⟨u.contained (h:=h) (hk:=hr) (hN:=hN) x⟩).2.1 -- namespace?
    have hδ': V.threshold=A.clock.threshold k:=by unfold V; rw [(h.wilson.represents N p k hN).vac];rfl
    let B:= 4*(b:ℝ)*ε;let W:= spine U 0;let t:= wired V.threshold 0 b U;let Z:=net V 0 b t
    have ht : 0<ε:=tau_pos _ _; have hB : 0≤ B :=by positivity
    obtain ⟨hx',hy',hz'⟩:=h3.1
    obtain ⟨H1,H2,H3⟩:= closer S u.length U H V.threshold V.threshold_pos ht hx'
    have hF : Agrees (Spindle.patch b (0:Site (C.side k p))) Z W := by
       intro j he hp; let i:Spindle.Dim (0:Site (C.side k p)) b:= ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ j,he,hp⟩⟩; exact (net_in V t i).trans (H2 i)
    have hZ: flags V.threshold Z=∅:= voids (occupied V t S (H1.trans (by change 2*B/V.threshold ≤ pane S; rw [hδ']; exact hy'))) le_rfl
    let T:= pull s 0 Z
    have hC: flags V.threshold T=∅:= by
       apply Finset.image_injective (f:=affine s 0) (Thirst.sends s (0:Site (C.side k p))).injective
       rw [show _=flags V.threshold Z from Work.H03.flags_send ..]; rw [hZ]; simp
    have hU: Healthy ε (Spindle.patch b 0) (pull s 0 W):=(s_healthy ..).mpr (by rw [Spindle.patch,swath_here]; unfold W Healthy spine; rw [gauge_flags]; exact H)
    have hV' (j): G.chord (Z j)≤B:= by
       by_cases hj:j ∈ Room (0:Site (C.side k p)) b
       · let g:Spindle.Dim (0:Site (C.side k p)) b:= ⟨j,hj⟩
         rw [hF _ (by exact (Finset.mem_filter.mp hj).2.1) (by exact (Finset.mem_filter.mp hj).2.2)]
         change G.chord (spine U _ g.val) ≤ _
         rw [spun U _ u.length]; apply ((played_cost _ _ ht.le (fun j=> chords b U ε H u.length j)).1).trans (mul_le_mul_of_nonneg_right _ ht.le)
         exact_mod_cast lengths_word G u.length g
       unfold Z; rw [net_out V _ _ hj,G.chord_one]; exact hB
    have heq : Agrees (Spindle.patch b (0:Site (C.side k p))) T (pull s 0 W):=s_locale s 0 (Spindle.patch b 0) Z W (by rw [Spindle.patch,swath_here];exact hF)
    let ρ:=Perch.bill (-J) L
    let X(f:C.label d):= paid C d k N p f
    let K:=a*ρ; have hb : ∀ y,0≤ X y:= fun y=>paid_pos ..
    have hK:0 ≤ K:=mul_nonneg ha.le (Real.exp_pos _).le
    have hg : ‖nearHol C x i k N p T - signet 0 η Wx T‖ ≤ K*X x:=by rw [(he x).locally _ _ heq,hf.locally _ _ heq]; exact h1 N hN p hr hW x _ (hP x) u _ hU
    have hD : ‖signet 0 η Wx T - signet 0 η (exchange (pivot s) Wx) Z‖≤ K*X x:=by
       apply (earn_ping s ht B u.length hV' hB (U:=U) H hF (show 0<η from inv_pos.mpr (Real.sqrt_pos.mpr (Overlay.beta_positive h.wilson hN))) Wx (qualified u hE hP x)).trans
       apply (mul_le_mul_of_nonneg_left (h2 N hN p) (sign _ _ zero_le_one)).trans;let E:= Perch.bill cκ L; have hA : 0 ≤ E:= (Real.exp_pos _).le
       -- raww factors bound using original blend and Mark charge.D use coin rise dustAt visit cost lengths (#cards).
       apply (mul_le_mul_of_nonneg_right hp' (Real.exp_pos _).le).trans
       change (Perch.bill 1 L* X x)* Perch.bill z L≤_
       rw [mul_right_comm (Perch.bill 1 L),overlap]; rw [one_mul] at h7; exact mul_le_mul_of_nonneg_right h7 (hb x)
    have hR' (x: C.label d) (U:Config G (C.side k p)) (hu:flags V.threshold U=∅): ‖wideHol C x i k N p U‖ ≤ K*X x:=by
       apply (wide_fare (hP x) U hu).trans
       apply (mul_le_mul (b:=Perch.bill z L) _ (mul_le_mul_of_nonneg_right hW (hb x)) (money_nn ..) (Real.exp_pos _).le).trans
       · rw [← mul_assoc]; apply mul_le_mul_of_nonneg_right _ (hb x); rw [overlap]; rw [one_mul] at h6; exact h6
       simpa only [neg_neg] using! h4 N hN p
    change ‖nearHol C q i k N p U- signet _ η (exchange (pivot s) Wx) U‖≤α*(X x+X q)
    rw [← (he q).inv (fingers U 0) U,← hc.inv (fingers U 0) U]
    rw [show Lattice.gauge (fingers U 0) U = W from rfl,← hc.locally Z W hF,← (he q).locally Z W hF]
    let f:= nearHol C q i k N p Z; let g:= nearHol C x i k N p T; let p1:=signet 0 η Wx T; let p2:=signet 0 η (exchange (pivot s) Wx) Z
    let N':=wideHol C q i k N p Z;let N'':=wideHol C x i k N p T
    have hz : f+N'=g+N'':= (sections_true h hr hN p i q Z hZ).trans (((hw d k hr N p hN s x).2 _ hZ).symm.trans (sections_true h hr hN p i x T hC).symm)
    change ‖f-p2‖≤_
    rw [show f-p2=(g-p1)+(p1-p2)+(N''-N') by rw [show f=g+N''-N' from eq_sub_of_add_eq hz]; abel]; refine (norm_add_le ..).trans ((add_le_add ((norm_add_le ..).trans (add_le_add hg hD)) ((norm_sub_le ..).trans (add_le_add (hR' x T hC) (hR' q Z hZ)))).trans ?_)
    change _≤α*(X x+X q); have hs:α = 4*K:=by dsimp only [α,K,a,ρ]; ring
    rw [hs]; linarith only [mul_nonneg hK (hb q),mul_nonneg hK (hb x)]
end YM.Next.Rank.East
