import YM.MultipleContact.Bunch.Box
import YM.MultipleContact.Matching.Read

/-! Passing comparable many-product bounds for genuine separated readings. -/
set_option autoImplicit false
noncomputable section
namespace YM.MultipleContact.Bunching
open Filter Function MeasureTheory Analysis Extraction Table Ward MergeProof Ribbons Around Cells Wilson Lattice Work.A01
open scoped Topology BigOperators Classical
open YM.Next.UVStress Matching Local

def lands {n m:ℕ}(y:Fin n → E4)(z:Points m) : Points (n+m):= points (Fin.append y z)
def many {G:Gauge}{L:Register G}{n m:ℕ}{S:Table L} (V:Fin n→S.Tag)(q:Fin m→L.Token) (y:Fin n → E4)(z:Points m) := disc (Fin.append V (S.classTokens∘q)) (lands y z)
section
variable {G:Gauge} {C : Family G} {S : Table C.book} {n' D h k N p: ℕ}(I:Watch C)(m:ℕ)
variable (x:(Fin n') → Cover) (_d:(Fin n') →ℕ)
def node:Points (n'+I.n) := lands (C.S.gridPoint m ∘ x) (Extraction.Order.grid C I.t I.x)
def levelsAt (n p:ℕ) := Fin.append (Cells.location C.S m n p ∘ x) (I.among n p)

lemma positioned (F:Extraction.Order)(v:(Fin n') →C.book.Token) (hp:F.PointLimits C S) (hv:node I m x∈generic _):
    Tendsto (fun u:ℕ×ℕ=>C.numeric u.1 u.2 (Fin.append v I.q) (levelsAt I m x u.1 u.2)) F.fuse
        (𝓝 (S.read (node I m x) (Fin.append v I.q))) := by
   let k:=max I.t m
   let U:= Fin.append (pushSite C.S (le_max_right I.t m) ∘ x) (pushSite C.S (le_max_left I.t m) ∘ I.x)
   have he : node I m x=Extraction.Order.grid C k U :=by
     ext1 i
     refine Fin.addCases (fun i=> by
                             unfold node Extraction.Order.grid lands; simp only [U,points_apply,Fin.append_left,Function.comp_apply]; rw [finer])
             (fun i=>by unfold node Extraction.Order.grid lands; simp only [U,points_apply,Fin.append_right,Function.comp_apply]; rw [finer]) i
   rw [he] at hv ⊢; refine (Extraction.Order.along (Cells.eventual_grid C F S hp U hv (Fin.append v I.q))).congr' ?_
   filter_upwards [large_mesh F k] with i hi
   apply congr_arg (C.numeric _ _ _); funext j
   refine Fin.addCases (fun j=>?_ ) (fun j=>?_) j
   · simp only [U,levelsAt,Fin.append_left,Function.comp_apply]; exact location_down C.S (le_max_right I.t m) hi _ _
   simp only [U,Fin.append_right,levelsAt,Watch.among,Function.comp_apply]; exact location_down C.S (le_max_left I.t m) hi _ _

private lemma frag (v : ∀ i:Fin n',C.book.Ref (_d i)) (z : C.book.Ref D)
    (N p : ℕ) (h e : ℝ) :
    moment (C.beta N p) (fun A => Bunching.loss C N p m D _d h e v x z A * I.plot N p A) =
      (↑(e^h):ℂ) * C.numeric N p
        (Fin.append (fun i:Fin n'=>(⟨_,v i⟩:C.book.Token)) I.q) (levelsAt I m x N p)-
          C.numeric N p (Fin.cons (α:=fun _ => C.book.Token) ⟨D,z⟩ I.q) (I.cuts N p) := by
  unfold moment; rw [C.num,C.num,← integral_const_mul,← integral_sub ((C.integrableR _ _).const_mul _) (C.integrableR _ _)]
  apply integral_congr_ae; filter_upwards with A
  rw [loss, Watch.plot]
  nth_rw 1 [Fin.prod_univ_succ]
  simp only [levelsAt,Fin.append_left,Fin.append_right,Bunching.node, Watch.cuts, Fin.prod_univ_add,Fin.cons_zero,Fin.cons_succ, Function.comp_apply, mul_assoc]
  dsimp only [Family.seen]; ring

lemma charge (F : Extraction.Order) (v : ∀i:Fin n',C.book.Ref (_d i))
    (hp : F.PointLimits C S) (H : S.Hierarchy) {f : Filter (ℕ×ℕ)} [f.NeBot] (hb : f ≤ F.fuse)
    (hv : node I m x ∈ generic _) (h e : ℝ) {V : ℕ × ℕ → C.book.Ref D} {p : C.book.Ref D} (ht : Tendsto V f (𝓝 p)) :
    let q := S.classTokens ∘ I.q
    Tendsto (fun u : ℕ×ℕ => moment (C.beta u.1 u.2) (fun A => Bunching.loss C u.1 u.2 m D _d h e v x (V u) A * I.plot u.1 u.2 A)) f
      (𝓝 ((↑(e^h):ℂ) * many (fun i:Fin n'=>⟨_,S.project (_d i) (v i)⟩) I.q (C.S.gridPoint m ∘ x) (Extraction.Order.grid C I.t I.x) -
        disc (Fin.cons ⟨D,S.project D p⟩ q) I.held)) := by
  intro q
  let first (v : C.book.Token) := Fin.cons (α:=fun _ => C.book.Token) v I.q
  have he := positioned I m x F (fun i:Fin n'=>(⟨_d i,v i⟩:C.book.Token)) hp hv |>.mono_left hb
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
  have hq : S.read (node I m x) (Fin.append (fun i:Fin n'=>⟨_d i,v i⟩) I.q) =
      many (fun i:Fin n'=>⟨_d i,S.project (_d i) (v i)⟩) I.q (C.S.gridPoint m ∘ x) (Extraction.Order.grid C I.t I.x) := by
    unfold node many; rw [← S.at_project S H.laws.toSymmetric (fun _ => le_rfl) (show lands .. ∈conf _ from generic_conf _ hv)]
    suffices e : S.classTokens ∘ (Fin.append (fun i:Fin n'=>⟨_d i,v i⟩) I.q) = Fin.append (fun i:Fin n'=>⟨_d i,S.project (_d i) (v i)⟩) (S.classTokens ∘ I.q) by rw [e]; rfl
    funext p; refine Fin.addCases (fun i=>?_ ) (fun j=>?_) p
    · change S.classTokens (Fin.append _ _ _)=_; rw [Fin.append_left,Fin.append_left]
    change S.classTokens (Fin.append _ _ _)=_; rw [Fin.append_right,Fin.append_right]; rfl
  have hf : S.read I.held (first ⟨D,p⟩)=disc (Fin.cons ⟨D,S.project D p⟩ q) I.held := by
    rw [← S.at_project S H.laws.toSymmetric (fun _ => le_rfl) I.distinct]; unfold first; rw [Work.A01.comp_cons]; rfl
  rw [← hf, ← hq]; exact ((he.const_mul ((↑(e^h):ℂ))).sub hh).congr (fun u => (frag ..).symm)

end
variable {G:Gauge} {C:Family G} {S : Table C.book}{F:Extraction.Order} {L:Register G}{D p J m j n':ℕ}

variable (H:S.Hierarchy) (hp:F.PointLimits C S)
variable {ι:Type*}{n:ι→ℕ}
variable (q:∀i:ι,Fin (n i)→ C.book.Token) (z:∀i:ι,Points (n i))
def bondedMany (q:∀ i:ι,Fin (n i)→ C.book.Token)(V:(Fin n') → S.Tag)(y:(Fin n') → E4)(r:ℝ)(D:ℕ)(z:∀ i,Points (n i))(v:S.Field D)(b ε:ℝ):Prop:=‖v‖≤b∧∀i,‖(r:ℝ) • many V (q i) y (z i)-Local.once (q i) ⟨D,v⟩ (z i)‖≤ ε
variable (hq:Cells.CellHyp C F)(hC:C.Makes)
variable (ℓ:∀i,Fin (n i)→ Cover){r A1 A2 h:ℝ}
set_option quotPrecheck false
variable {d:(Fin n') →ℕ}(V:∀ i:Fin n',C.book.Ref (d i)) (hL:∀ i,Injective (Fin.cons (α:=fun _=>Cover) 0 (ℓ i))) (hr:0<r)
include H hp hC hq hL hr
variable {lamp:Lattice.Side}
lemma readGrid [Fintype ι][Inhabited (Fin n')]:∃wgt> (0:ℝ),∀ V (m j D:ℕ), ∀ h A1 A2:ℝ, Bunching.Box C J j m D d h V F lamp A1 A2 → ∀ η:∀ i,Fin (n i)→ Cover, ∀ κ:ℕ, (∀ i, Order.grid C κ (Fin.cons 0 (η i)) ∈ generic (n i+1)) → ∀ y':(Fin n') → Cover, y' default=0 → (∀s t:Fin n',s≠t → (fuga C.path.levels (m+1))/16≤ ‖C.S.gridPoint j (y' s-y' t)‖)→ (∀ s:Fin n',‖C.S.gridPoint j (y' s)‖≤4*topZone C.path.levels (lamp*C.S.block m) (m+1)) → ∀z:∀i,Points (n i), (∀ i, z i=Order.grid C κ (η i)) → (∀ i,Locations C J r (ℓ i) (z i))→ (∀ i,lands (C.S.gridPoint j ∘ y') (z i)∈generic _) → ∃ v:S.Field D, bondedMany q (fun i:Fin n'=>⟨d i,S.project (d i) (V i)⟩) (C.S.gridPoint j ∘ y') ((fuga C.path.levels (m+1))^h) D z v (‖LinearMap.toContinuousLinearMap (S.project D)‖* A1) (wgt*A2):= by
    choose a ha h' using fun i=> Local.acornsS C (q i) hC hq J (ℓ i) (hL i) hr
    obtain ⟨x,hx⟩:=Finite.bddAbove_range a
    refine ⟨max 1 x,lt_of_lt_of_le zero_lt_one (le_max_left ..),fun V m j D h A1 A2 hBox η κ hY y hx0 h₁ h₂ z hz' hZ hz=>?_⟩

    let r':=(fuga C.path.levels (m+1))
    obtain ⟨w,hw⟩:= hBox.corners y hx0 h₁ h₂
    have hp':∀ᶠ u: ℕ×ℕ in F.fuse,‖w u‖ ≤ A1:=show F.late fun N p=> ‖w (N,p)‖ ≤ A1 from hw.mono fun N he=>he.mono fun p hh=> hh.choose_spec.1
    obtain ⟨b,hb,Hb,c,hE⟩:= finite_extract (𝓛:=F.fuse) w A1 hp'
    let v := S.project D c
    refine ⟨v,(LinearMap.toContinuousLinearMap (S.project D)).le_opNorm _ |>.trans (mul_le_mul_of_nonneg_left (le_of_tendsto hE.norm (hp'.filter_mono hb)) (norm_nonneg _)),fun i=>?_⟩
    let I:Watch C:=⟨n i,κ,η i,q i,hY i⟩
    let ε:=A2
    have hI: I.held = Points.cons 0 (z i):=by rw [hz' i]; ext1 k;exact Fin.cases (show _ from Watch.origin _) (fun j=> (rfl)) k
    specialize h' i _ _ (hY i) (fun k a=>by specialize hZ i k a; rw [hz' i] at hZ; exact hZ)
    change ‖(r'^h:ℝ) • many _ _ _ (z i) - disc (Fin.cons (α:=fun _=>S.Tag) _ (S.classTokens∘q i)) (Points.cons 0 (z i))‖ ≤ _
    rw [← hI];
    have htG:= hz i; rw [hz' i] at htG
    have hm := ((charge I j y d F V hp H hb (D:=D) htG h r' hE).norm)
    rw [hz' i]
    apply le_of_tendsto (show Tendsto _ b (𝓝 _) from hm)
    apply Eventually.filter_mono hb
    let g (u : ℕ×ℕ) := Bunching.loss C u.1 u.2 j D d h r' V y (w u)
    have ht : ∀ᶠ u : ℕ×ℕ in F.fuse, ∃ hN:J≤u.1,
      ‖w u‖ ≤ A1 ∧ Cells.Interior ((center C.S u.2 hN 0).chamber 0) (g u) ∧
        (center C.S u.2 hN 0).rootTest (C.beta u.1 u.2) (g u) ≤ ε := hw
    filter_upwards [ht,h'] with u hu hv
    obtain ⟨hN,-,H',HL⟩:=hu; obtain ⟨_,hv⟩ := hv
    apply le_trans (hv (g u) H')
    refine (mul_le_mul_of_nonneg_right HL (ha i)).trans ?_
    rw [mul_comm (max 1 x)]; apply mul_le_mul_of_nonneg_left ((hx (Set.mem_range_self _)).trans (le_max_right ..)) (le_trans ((center C.S u.2 hN 0).root_nonneg ..) HL)
end YM.MultipleContact.Bunching
