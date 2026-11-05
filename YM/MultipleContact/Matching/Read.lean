import YM.MultipleContact.FieldBound
import YM.MultipleContact.Matching.Seam

/-! Passing comparable pair estimates to grid readouts, simultaneous across exteriors. -/
set_option autoImplicit false
noncomputable section
namespace YM.MultipleContact.Local
open Filter Function MeasureTheory Analysis Extraction Table Ward MergeProof Ribbons Around Cells Wilson Lattice Work.A01
open scoped Topology BigOperators Classical
open YM.Next.UVStress
section
variable {G:Gauge} {C : Family G} {S : Table C.book} {d D h k N p t: ℕ}(I:Watch C)(i_unused:Prop)(m:ℕ)(x:Cover)
private lemma frag (v : C.book.Ref t) (w : C.book.Ref d) (z : C.book.Ref D)
    (N p : ℕ) (h e : ℝ) :
    moment (C.beta N p) (fun A => Matching.residue (C:=C) (d:=d) (D:=D) h e v w m x N p z A * I.plot N p A) =
      (↑(e^h):ℂ) * C.numeric N p
        (Fin.cons (α:=fun _ => C.book.Token) ⟨t,v⟩ (Fin.cons (α:=fun _ => C.book.Token) ⟨d,w⟩ I.q)) (I.layers m x N p)-
          C.numeric N p (Fin.cons (α:=fun _ => C.book.Token) ⟨D,z⟩ I.q) (I.cuts N p) := by
  unfold moment; rw [C.num,C.num,← integral_const_mul,← integral_sub
    ((C.integrableR _ _).const_mul _) (C.integrableR _ _)]
  apply integral_congr_ae; filter_upwards with A
  rw [Matching.residue, Watch.plot]
  nth_rw 2 [Fin.prod_univ_succ]
  -- explicitly order
  simp only [Watch.layers,Watch.cuts,Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,mul_assoc]
  dsimp only [Family.seen]
  ring

/-- Limit of the genuine signed comparison. Coefficients can vary with
cutoffs (NeBot subfilter used ONLY in checking continuum estimates).
-/
lemma charge (F : Extraction.Order) (v : C.book.Ref t) (w : C.book.Ref d)
    (hp : F.PointLimits C S) (H : S.Hierarchy) {f : Filter (ℕ×ℕ)} [f.NeBot] (hb : f ≤ F.fuse)
    (hv : I.point m x ∈ generic _) (h : ℝ) (e : ℝ) {V : ℕ × ℕ → C.book.Ref D} {p : C.book.Ref D} (ht : Tendsto V f (𝓝 p)) :
    let q := S.classTokens ∘ I.q
    Tendsto (fun u : ℕ×ℕ => moment (C.beta u.1 u.2) (fun A => Matching.residue (C:=C) (d:=d) (D:=D)
      h e v w m x u.1 u.2 (V u) A * I.plot u.1 u.2 A)) f
      (𝓝 ((↑(e^h):ℂ) * disc (Fin.cons ⟨t,S.project t v⟩ (Fin.cons ⟨d,S.project d w⟩ q)) (I.point m x) -
        disc (Fin.cons ⟨D,S.project D p⟩ q) I.held)) := by
  intro q
  let first (v : C.book.Token) := Fin.cons (α:=fun _ => C.book.Token) v I.q
  let second (v' w' : C.book.Token) := Fin.cons (α:=fun _ => C.book.Token) v' (first w')
  have he := I.placed m x ⟨t,v⟩ ⟨d,w⟩ hp hv |>.mono_left hb
  have hh : Tendsto (fun u : ℕ×ℕ => C.numeric u.1 u.2 (first ⟨D,V u⟩) (I.cuts u.1 u.2)) f
      (𝓝 (S.read I.held (first ⟨D,p⟩))) := by
    let g (u : ℕ×ℕ) := C.ensemble (readDegrees (v:=I.q) D) (I.cuts u.1 u.2)
    have hx (a : C.book.Ref D) (u : ℕ×ℕ) : C.numeric u.1 u.2 (first ⟨D,a⟩) (I.cuts u.1 u.2)= g u (vals I.q a) := by
      rw [show first ⟨D,a⟩=(fun i => (⟨readDegrees (v:=I.q) D i,vals I.q a i⟩ : C.book.Token)) from ?_]; rfl
      funext i; refine Fin.cases (show first _ 0 = _ from (by rw [show first ⟨D,a⟩ 0=⟨D,a⟩ from Fin.cons_zero ..]; rfl)) (fun j => ?_) i
      unfold first; rw [Fin.cons_succ]; rfl
    let L (u : ℕ×ℕ) := LinearMap.toContinuousLinearMap
      (show C.book.Ref D→ₗ[ℂ] ℂ from (g u).toLinearMap (vals I.q (0:C.book.Ref D)) 0)
    have hy (a : C.book.Ref D) (u : ℕ×ℕ) : L u a = C.numeric u.1 u.2 (first ⟨D,a⟩) (I.cuts u.1 u.2) := by
      rw [hx]; change g u (update (vals I.q (0:C.book.Ref D)) 0 (headValue I.q a))=_; rw [← update_front]
    have hz (a : C.book.Ref D) : Tendsto (fun u : ℕ×ℕ => (L u).toLinearMap a) f (𝓝 (S.injectFront I.q I.held D a)) :=
      ((I.single_lim ⟨D,a⟩ hp).mono_left hb).congr fun u => (hy a u).symm
    exact (Dash.arcing (Dash.fit_plane (fun u => (L u).toLinearMap) (S.injectFront I.q I.held D) hz) ht).congr (fun u => hy _ _)
  have hq : S.read (I.point m x) (second ⟨t,v⟩ ⟨d,w⟩) =
      disc (Fin.cons ⟨t,S.project t v⟩ (Fin.cons ⟨d,S.project d w⟩ q)) (I.point m x) := by
    rw [← S.at_project S H.laws.toSymmetric (fun _ => le_rfl) (generic_conf _ hv)]; unfold second first; rw [Work.A01.comp_cons, Work.A01.comp_cons]; rfl
  have hf : S.read I.held (first ⟨D,p⟩)=disc (Fin.cons ⟨D,S.project D p⟩ q) I.held := by
    rw [← S.at_project S H.laws.toSymmetric (fun _ => le_rfl) I.distinct]; unfold first; rw [Work.A01.comp_cons]; rfl
  rw [← hf, ← hq]; exact ((he.const_mul ((↑(e^h):ℂ))).sub hh).congr (fun u => (frag ..).symm)

end
variable {G:Gauge} {C:Family G} {S : Table C.book}{F:Extraction.Order} {L:Register G}{t d D p J m j:ℕ}
variable (H:S.Hierarchy) (hp:F.PointLimits C S)
variable {ι:Type*}{n:ι→ℕ}
-- All exterior labels initially reference literal labels. No requirement on support positions aside from cell clearance and Conf.
variable (q:∀i:ι,Fin (n i)→ C.book.Token) (z:∀i:ι,Points (n i))
def once {n':ℕ}(q:Fin n' → C.book.Token)(v:S.Tag)(z:Points n'):= disc (Fin.cons v (S.classTokens∘q)) (Points.cons 0 z)  -- change (Points.cons 0 z)
-- pair T at y, B at origin
def twice {n':ℕ}(q:Fin n' → C.book.Token)(V B:S.Tag)(y:E4)(z:Points n'):= disc (Fin.cons V (Fin.cons B (S.classTokens∘q))) (Points.cons y (Points.cons 0 z))
def bonded (q:∀ i:ι,Fin (n i)→ C.book.Token)(V B:S.Tag)(y:E4)(r:ℝ)(D:ℕ)(z:∀ i,Points (n i))(v:S.Field D)(b ε:ℝ):Prop:=‖v‖≤b∧∀i,‖(r:ℝ) • twice (q i) V B y (z i)-once (q i) ⟨D,v⟩ (z i)‖≤ ε
variable (hq:Cells.CellHyp C F)(hC:C.Makes)
variable (ℓ:∀i,Fin (n i)→ Cover){r A1 A2 h:ℝ}
set_option quotPrecheck false
-- broad annulus
variable (V:C.book.Ref t)(B:C.book.Ref d)(hL:∀ i,Injective (Fin.cons (α:=fun _=>Cover) 0 (ℓ i))) (hr:0<r)
include H hp hC hq hL hr
open Matching
lemma readGrid [Fintype ι]:∃A> (0:ℝ),∀ V B (m j D:ℕ), ∀ h A1 A2:ℝ, Box C J j m D d t h B V F A1 A2 → ∀ η:∀ i,Fin (n i)→ Cover, ∀ κ:ℕ, (∀ i, Order.grid C κ (Fin.cons 0 (η i)) ∈ generic (n i+1)) → ∀ y':Cover, (fuga C.path.levels (m+1))/16≤ ‖C.S.gridPoint j y'‖ → ‖C.S.gridPoint j y'‖≤4*topZone C.path.levels (C.S.block m) (m+1) → ∀z:∀i,Points (n i), (∀ i, z i=Order.grid C κ (η i)) → (∀ i,Locations C J r (ℓ i) (z i))→ (∀ i,Points.cons (C.S.gridPoint j y') (Points.cons 0 (z i))∈generic _) → ∃ v:S.Field D, bonded q ⟨t,S.project t V⟩ ⟨d,S.project d B⟩ (C.S.gridPoint j y') ((fuga C.path.levels (m+1))^h) D z v (‖LinearMap.toContinuousLinearMap (S.project D)‖* A1) (A*A2):= by
    choose a ha h' using fun i=> Local.acornsS C (q i) hC hq J (ℓ i) (hL i) hr
    obtain ⟨x,hx⟩:=Finite.bddAbove_range a
    refine ⟨max 1 x,lt_of_lt_of_le zero_lt_one (le_max_left ..),fun V B m j D h A1 A2 hBox η κ hY y h₁ h₂ z hz' hZ hz=>?_⟩

    let r':=(fuga C.path.levels (m+1))
    obtain ⟨w,hw⟩:= hBox.corners y h₁ h₂
    have hp':∀ᶠ u: ℕ×ℕ in F.fuse,‖w u‖ ≤ A1:=show F.late fun N p=> ‖w (N,p)‖ ≤ A1 from hw.mono fun N he=>he.mono fun p hh=> hh.choose_spec.1
    obtain ⟨b,hb,Hb,c,hE⟩:= finite_extract (𝓛:=F.fuse) w A1 hp'
    let v := S.project D c
    refine ⟨v,(LinearMap.toContinuousLinearMap (S.project D)).le_opNorm _ |>.trans (mul_le_mul_of_nonneg_left (le_of_tendsto hE.norm (hp'.filter_mono hb)) (norm_nonneg _)),fun i=>?_⟩
    let I:Watch C:=⟨n i,κ,η i,q i,hY i⟩
    let ε:=A2
    have hI: I.held = Points.cons 0 (z i):=by rw [hz' i]; ext1 k;exact Fin.cases (show _ from Watch.origin _) (fun j=> (rfl)) k
    specialize h' i _ _ (hY i) (fun k a=>by  specialize hZ i k a; rw [hz' i] at hZ; exact hZ)
    change ‖(r'^h:ℝ) • disc _ _ - disc (Fin.cons (α:=fun _=>S.Tag) _ (S.classTokens∘q i)) (Points.cons 0 (z i))‖ ≤ _
    rw [← hI];
    have hm := ((charge I j y F (d:=d) V B hp H hb (show I.point j y∈generic _ from show Points.cons _ I.held∈_ from hI ▸ hz i) h r' hE).norm) -- hm target rewrite
    apply le_of_tendsto (show Tendsto _ b (𝓝 _) from hm) -- replace
    apply Eventually.filter_mono hb
    let g (u : ℕ×ℕ) := Matching.residue (C:=C) (d:=d) (D:=D) h r' V B j y u.1 u.2 (w u)
    have ht : ∀ᶠ u : ℕ×ℕ in F.fuse, ∃ hN:J≤u.1,
      ‖w u‖ ≤ A1 ∧ Cells.Interior ((center C.S u.2 hN 0).chamber 0) (g u) ∧
        (center C.S u.2 hN 0).rootTest (C.beta u.1 u.2) (g u) ≤ ε := hw
    filter_upwards [ht,h'] with u hu hv
    obtain ⟨hN,-,H',HL⟩:=hu; obtain ⟨_,hv⟩ := hv
    apply le_trans (hv (g u) H')
    refine (mul_le_mul_of_nonneg_right HL (ha i)).trans ?_
    rw [mul_comm (max 1 x)]; apply mul_le_mul_of_nonneg_left ((hx (Set.mem_range_self _)).trans (le_max_right ..)) (le_trans ((center C.S u.2 hN 0).root_nonneg ..) HL)
end YM.MultipleContact.Local
