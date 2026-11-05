import YM.Bid.Angular

/-! Use-site of angular bids. Also red Outer. -/
set_option autoImplicit false
noncomputable section
namespace YM.Bid
open Set Function Filter Org Spec Extraction Climb Table Ward Spin
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius NNReal InnerProductSpace

variable {G : Gauge} {L : Register G} {S : Table L}

/-- OUTER red. No circular requests downstream -/
def Miles : Prop := ∀ {G : Gauge} {C : Family G} {F : Order} {S : Table C.book} (V : DiffPlan S) (W : MaxwellData C) (I : IR (C:=C) S)
    (_ : UV C F S V W I), V.Inclusions S → V.Derivatives S →
    LineSum I.p ∧ (∀ K a n (q : Fin n → S.Tag) (x : Points n), x∈conf _ → onLine a x → localTurn I.p I.Y K q x=0)

section
variable {C : Family G} {F : Order} {S : Table C.book} (W : MaxwellData C) (V : DiffPlan S) (I : IR (C:=C) S) (H : UV C F S V W I)

private abbrev funded (B : Scaling S→ Prop) := Watches I.J W.T H.basis.kernel.spin W.hT.spin V B
private theorem buysBoth {L P : Scaling S → Prop} (h : funded W V I H L) (hp : funded W V I H P) :
    funded W V I H (fun p => L p ∧ P p) := by
  obtain ⟨d,n,m,r,ht,hL⟩ := h.ask
  obtain ⟨e,i,j,s,hy,hQ⟩ := hp.ask
  refine ⟨max d e,max n i,max m j,max r s,le_max_of_le_left ht,fun T c v t K Ha Hb Hc Hd A => ?_⟩
  exact ⟨hL T c v t K (by omega) (by omega) (by omega) ((le_max_left _ _).trans Hd) A,
    hQ T c v t K (by omega) (by omega) (by omega) ((le_max_right _ _).trans Hd) A⟩
private theorem selects {L : Scaling S→Prop} (h : funded W V I H L) : ∃ X,L X := by
  obtain ⟨u,v,z,c,r,h⟩ := h.ask
  obtain ⟨i,hi⟩ := H.weak.connects _ _ _ _ r
  exact ⟨_,h i u v z c le_rfl le_rfl le_rfl le_rfl hi⟩

private lemma witnessing (A : A01) (B : A02) (Y : A03) (x : Miles) (hx : V.Inclusions S) (hp : V.Derivatives S) :
    Shapes H.basis.kernel V I.J I.p I.Y ∧ ShellCom V I.p I.Y ∧ Hyper H.basis.kernel.spin V I.Y ∧ Climb.transverse V.deriv := by
  obtain ⟨h,hT⟩ := A H.basis.kernel V hp hx H.aligned I.J I.p I.Y H.planet
  have hb := B H.basis.kernel V hp hx I.J I.p I.Y H.planet
  obtain ⟨ht,hu⟩ := x _ _ _ H hx hp
  obtain ⟨hf,hY⟩  := Y H.basis.kernel V hx hp H.aligned I.p I.Y h hb ht
  exact ⟨⟨H.planet,h,hf,hu⟩,hb,hT,hY⟩

private lemma lmul {S : Table L} (W : DiffPlan S) (d : ℕ) (v : ℝ) : leaves (v • W.deriv) d=v • leaves W.deriv d := by ext1 i;ext1 x;rfl

private lemma awake {Y : Table L} (X : Scaling Y) {P d R t} (h : ConLap X P d R t) (hh : leaves R d≠0) : leaves P d≠0 := by
  unfold ConLap at h; intro he; rw [he] at h; simp only [map_zero] at h
  have ht (i : ℕ) : t i • (0:Climb.Vector d (Bel L))=0 := by ext1 j; ext1 k; simp
  simp_rw [ht] at h
  exact hh (tendsto_nhds_unique h tendsto_const_nhds)

private lemma pressured (h : V.Inclusions S) (hx : V.Derivatives S) (hp : Shapes H.basis.kernel V I.J I.p I.Y)
    (hv : Climb.transverse V.deriv) (A : A04) (B : A05) (C' : A06) : ∃ c : ℝ,c≠0 ∧ ∀ d, leaves I.p d=c • leaves V.deriv d := by
  obtain ⟨d,hD⟩ := W.lit.cuts
  refine extends_form V W.T.W H.basis.kernel I.p h (native _ H.basis.kernel h hx H.aligned) hp.rights (a:=W.hT.spin) ⟨d,?_⟩
  intro i hi; obtain ⟨Sx,hT⟩ := hD i hi
  obtain ⟨X,hH, hZ⟩ := selects W V I H (buysBoth W V I H
    (buysBoth W V I H (A H.basis.kernel V h hx W I.J i) (B H.basis.kernel V h hx W I.J i _ _ hp.local_))
      (C' H.basis.kernel V h hx W I.J i I.p hp.fills hv hp.rights Sx hT))
  obtain ⟨ht,Z,hz⟩ := (show _ ∧ _ from hZ)
  exact ⟨⟨X,Sx,Z,ht,hT,hz⟩, awake X hH.1 hT.nz, awake X hH.2.1 (by
    rw [lmul]; exact smul_ne_zero W.T.hκ hT.nz)⟩

private lemma formed {c : ℝ} (hc : c≠0) (h : ShellCom V I.p I.Y) (hp : Shapes H.basis.kernel V I.J I.p I.Y)
    (ht : ∀ d, leaves I.p d = c • leaves V.deriv d) : Crystal H.basis.kernel V I.J I.p I.Y c := by
  have he (d ν u) : I.p d ν u=(c:ℂ) • V.deriv d ν u :=
    Eq.trans (congr_arg (fun g : Climb.Vector d S => g ν u) (ht d)) (RCLike.real_smul_eq_coe_smul (K:=ℂ) c _)
  have HH (d g u) : ((c⁻¹:ℝ) • I.Y : SpinRows S) d g u=((c:ℂ)⁻¹) • I.Y d g u := by
    rw [← Complex.ofReal_inv]; exact (RCLike.real_smul_eq_coe_smul (K:=ℂ) c⁻¹ _)
  refine ⟨hc,hp,ht, ?_,?_⟩
  · intro d t b p; rw [HH,HH,map_smul,← h.moves,smul_add]; congr 1
    simp_rw [Finset.smul_sum]; apply Finset.sum_congr rfl; intro i _; rw [he,smul_comm _ (↑(t.val i b) : ℂ),inv_smul_smul₀ (by exact_mod_cast hc)]
  intro a n K q x hx ht; have hz := hp.orient K a n q x hx ht
  have hw (i : Fin n) : (c:ℂ) • disc (update q i (turns (c⁻¹ • I.Y) K (q i))) x=disc (update q i (turns I.Y K (q i))) x := by
    unfold turns; simp_rw [← takes,HH]; rw [← map_smul, smul_inv_smul₀ (by exact_mod_cast hc)]
  apply smul_right_injective ℂ (show (c:ℂ)≠0 by exact_mod_cast hc)
  dsimp only
  rw [smul_zero, ← hz]; unfold angular localTurn
  simp_rw [Finset.smul_sum]; apply Finset.sum_congr rfl; intro i _; rw [smul_add,hw,Finset.smul_sum]; congr 1
  apply Finset.sum_congr rfl; intro j _; rw [he,← takes,← takes,map_smul,smul_comm]
  rfl

private lemma currencies {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] {X : ℕ → Z} {x : Z}
    (k : ℝ) (f : ℕ → ℝ) (hx : Tendsto X atTop (𝓝 x)) (ht : Tendsto (fun i => f i • X i) atTop (𝓝 (k • x))) (h : x≠0) : Tendsto f atTop (𝓝 k) := by
  obtain ⟨Y,hY⟩ := Module.Projective.exists_dual_ne_zero ℝ h
  have hc := Y.continuous_of_finiteDimensional
  have he := hc.continuousAt.tendsto.comp ht; have hv := hc.continuousAt.tendsto.comp hx
  have hp := he.div hv hY
  rw [map_smul,smul_eq_mul, mul_div_cancel_right₀ _ hY] at hp
  apply hp.congr'
  filter_upwards [hv.eventually (isOpen_compl_singleton.mem_nhds hY)] with i hi
  change Y (f i • X i)/Y (X i)= _
  rw [map_smul, smul_eq_mul,mul_div_cancel_right₀ _ (show Y (X i) ≠ 0 from hi)]

private theorem hyper (H : S.RealSpin) (V : DiffPlan S) (Y : SpinRows S) (h : Hyper H V Y) (c : ℝ) : Hyper H V (c • Y) where
  real d u v := by
    change S.conj H d (c • Y d u v)=c • Y d u (S.conj H d v)
    simp only [RCLike.real_smul_eq_coe_smul (K:=ℂ),map_smulₛₗ,h.real]; simp
  inter d e w u v := by
    change c • Y e u _=V.rise w (c • Y d u v); simp only [RCLike.real_smul_eq_coe_smul (K:=ℂ),h.inter,map_smul]
  unity d u := by change c • Y d u (S.unit d)=0; simp [h.unity]
  hex d g u v := by
    change S.mirror H d g (c • Y d u v)=c • Y d (orients g u) _; simp only [RCLike.real_smul_eq_coe_smul (K:=ℂ),h.hex,map_smul]

private lemma imaginary {L : Register G} {S : Table L} (d) {X : SpinRows S} {Y : SpinRows (Bel L)} (hu : Brackets X)
    (ht : Brackets Y) (v : Spin.change S d) (z : List ℝ) (i : Spin.Ind) (A : A09) :
    Commute (wave z (transport X v) (leaf Y d)) (effect (transport X v i) (leaf Y d i)) := by
  classical
  -- transport at this cap; pad others default with free.
  let b : Ortho.Skew→ₗ[ℝ] ((Bel L).Field d→ₗ[ℂ] (Bel L).Field d) := {
    toFun t := v.symm.toLinearMap ∘ₗ ((X d t) ∘ₗ v.toLinearMap)
    map_add' i j := by ext u; simp
    map_smul' a t := by
      apply LinearMap.ext; intro u
      change v.symm (X d (a • t) (v u))=a • v.symm _
      rw [map_smul]; exact (v.symm.toLinearMap.restrictScalars ℝ).map_smul a _ }
  let F := update Y d b
  have hf : Brackets F := by
    intro n g k; by_cases h : n=d
    · subst n; unfold F; rw [update_self]; apply LinearMap.ext; intro u
      have he := LinearMap.congr_fun (hu d g k) (v u)
      apply v.injective; simpa [b] using! he -- needs coe rewrites
    rw [show F n=Y n from update_of_ne h ..]; exact ht n g k
  have hp : leaf F d=transport X v := by unfold leaf transport; simp only [F,update_self]; rfl
  rw [← hp]; exact (A F hf).2 Y ht d z i

private lemma services (w : V.Inclusions S) (p : V.Derivatives S) {c : ℝ} (h : Crystal H.basis.kernel V I.J I.p I.Y c)
    (A : A01) (U1 : A04) (M1 : A05) (B1 : A07) (D1 : A08) (O1 : A09) (T1 : A10) (Y1 : A11)
    (hv : ∀ n (x : Points n), x∈conf _ → Still V (c⁻¹ • I.Y) x) (d : ℕ) : ∃ U z,Spin.Tilt W.T.K H.basis.kernel.spin W.hT.spin (c⁻¹ • I.Y) d U z := by
  have hu := U1 H.basis.kernel V w p W I.J 4
  have heA : funded W V I H (fun Q => Q.Align V W.T.W H.basis.kernel.spin W.hT.spin d) := by
    refine ⟨d,0,0,1,le_rfl,fun q u t a b hh hk hl hy hz => ?_⟩
    have hw : d ≤ max u 4 := hh.trans (le_max_left ..)
    exact ⟨fun k e h => hz.path.Hsym k _ (h.trans hw),fun k e h => hz.path.carries k _ (h.trans hw),fun k e t g l v => hz.path.incl k e t g (l.trans hw) v⟩
  obtain ⟨Q,hp,hm,ht,hT⟩ := selects W V I H (buysBoth W V I H hu (buysBoth W V I H
      (M1 H.basis.kernel V w p W I.J 4 I.p I.Y H.planet) (buysBoth W V I H
        (M1 H.basis.kernel V w p W I.J d I.p I.Y H.planet) heA)))
  · have hg : Tendsto (fun i => c/Q.xi i) atTop (𝓝 W.T.κ) := by
      refine currencies (X:=fun i => Q.r i • Q.aisle i 4 (leaves V.deriv 4)) _ (fun i => c/Q.xi i) hp ?_ W.lit.born
      have hz := hm.1
      unfold ConLap at hp hz; rw [lmul,h.sizes] at hz; simp_rw [map_smul, smul_smul] at hz
      exact hz.congr (fun i => by rw [smul_smul,show Q.r i/Q.xi i*c=c/Q.xi i*Q.r i by ring])
    obtain ⟨z,hz⟩ := W.marks d
    have hi := hyper H.basis.kernel.spin _ _ (A H.basis.kernel V p w H.aligned I.J I.p I.Y H.planet).2 c⁻¹
    have hh := D1 H.basis.kernel V w p H.aligned (c⁻¹ • I.Y) hv hi (B1 H.basis.kernel V w p H.aligned W I.J H.weak)
    have he (i) := hT.Hsym i d le_rfl
    refine ⟨fun i => Q.U i d,z,he,fun j => ?_,(O1 _ hh).1,W.optic,hz, Eventually.of_forall fun x => ⟨Y1 T1 _ _ _ hi W d _ (he x) _,fun i => ?_⟩⟩
    · have hr := hg.inv₀ W.T.hκ |>.smul (ht.2 j)
      rw [inv_smul_smul₀ W.T.hκ] at hr
      refine hr.congr (fun i => ?_)
      dsimp only
      have he : (c/Q.xi i)⁻¹*(Q.xi i)⁻¹ = c⁻¹ := by field_simp [(Q.sign i).ne',h.positive]
      change (c/Q.xi i)⁻¹ • ((Q.xi i)⁻¹ • _) = _
      rw [smul_smul,he]; ext1 v
      let B := Q.U i d
      change c⁻¹ • B.symm _=B.symm (c⁻¹ • I.Y d _ _)
      exact ((B.symm.toLinearMap.restrictScalars ℝ).map_smul _ _).symm
    apply imaginary (X:=c⁻¹ • I.Y) d hh (Y:=W.T.K.lie) _ (Q.U x d) z i O1
    have he := W.lit.turns
    exact (T1 W.hT.spin W.T.K ⟨he.spin,he.fixes,he.group,he.signed,he.real,he.infinitesimal⟩).1

lemma station (A : Miles) (B : A01) (C' : A02) (D : A03) (D' : A04) (F' : A05) (E : A06) (G' : A07) (J : A08)
    (K : A09) (U : A10) (O : A11) (R : A13) (T : A14) (P : A15) (Q : A16) (Z : A17) : Commission V W I H where
  shape i p := (witnessing W V I H B C' D A i p).1
  scales u v k := by
    have he := witnessing W V I H B C' D A u v; obtain ⟨c,hc,hh⟩ := pressured W V I H u v k he.2.2.2 D' F' E
    exact ⟨_,formed W V I H hc he.2.1 k hh⟩
  lens u v c h s d := services W V I H u v h B D' F' G' J K U O s d
  group c i u v a b := T R H.basis.kernel V u v _ a b
  retune c i u v b t a := P U _ V u v H.aligned _ t a I.J I.p I.Y c b rfl
  generate c t j S := Z Q _ _ _ H c t j S
end
end YM.Bid
