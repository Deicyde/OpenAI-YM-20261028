import YM.OPE.Orbits.Stars

/-! Kernels for comparing readouts against a physical approximate field.
Plus-notation only for concatenating exterior names using Table symmetry.
Unit terms are those of the actual expectations. No connected-log discard. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Orbits
open Function Filter Set MeasureTheory Extraction Table Reader Prescription
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
attribute [local instance] measO
variable {G:Gauge}{L:Register G}{S T:Table L}{Q:DiffPlan S}{ρ:S.RealSpin}{X:S.Rotation}{I J K:Type}[Fintype I][Fintype J]{d:I→ℕ}{e:J→ℕ}{t:K→ℕ}

-- same `beside` weight diagram, name fields scoped.
def whole (T:Table L)(x:I→E4)(v:Labels S d)(y:J→E4)(w:Labels S e):ℂ:=moment T (beside x y) (stages v w)
lemma whole_observed (x:I→E4)(v:Labels S d)(y:J→E4)(w:Labels S e): whole T x v y w=observe T (beside x y) (beside (names v) (names w)):=by
    rw [whole,observed]; exact congr_arg _ (funext fun q=>by cases q <;> rfl)
lemma whole_perm (T:Table L){I' J':Type}[Fintype I'][Fintype J'](k:I'≃I)(q:J'≃J){x:I→ E4}{v:Labels S d}{y:J→E4}{w:Labels S e}(hT:T.Hierarchy)(hx:Injective (beside x y)):
    whole T (x ∘ k) (fun i=> (v (k i):S.Field ((d ∘ k) i))) (y ∘ q) (fun j=>(w (q j):S.Field ((e ∘ q) j)))=whole T x v y w:=by
    simp only [whole_observed]; convert perm_observe T hT.laws.toSymmetric (Equiv.sumCongr k q) (beside (names v) (names w)) hx using 2 <;> try rfl
    all_goals funext i; cases i<;> rfl  -- maybe no goals
lemma whole_flip (v:Labels S d)(w:Labels S e)(x:I→ E4)(y:J→ E4)(hT:T.Hierarchy)(hx:Injective (beside x y)):
    whole T y w x v = whole T x v y w:=by
    simp only [whole_observed]; convert perm_observe T hT.laws.toSymmetric (Equiv.sumComm J I) (beside (names v) (names w)) hx using 2 <;> try rfl
    all_goals funext j; cases j <;> rfl

def upon (T:Table L)(m:ℕ)(o:E4)(y:J→ E4)(w:Labels S e):S.Field m→ₗ[ℂ] ℂ where
    toFun c:= whole T (sole o) (sole c: Labels S (fun _:Unit=>m)) y w
    map_add' c z:= by
       classical
       have hv(c:S.Field m):whole T (sole o) (sole c:Labels S (fun _:Unit=>m)) y w=sectionLabels (d:=Sum.elim (fun _:Unit=>m) e) w (m:=moment T (beside (sole o) y)) (sole c):=sectionLabels_apply .. |>.symm
       rw [hv,hv,hv];
       have hf(c:S.Field m):sole c= update (β:=fun _:Unit=>S.Field m) 0 () c:=(funext (fun i=>by cases i; exact (show update (β:=fun _:Unit=>S.Field m) 0 () c ()=c from Function.update_self (β:=fun _:Unit=>S.Field m) () c 0).symm))
       simp_rw [hf]; apply MultilinearMap.map_update_add ..
    map_smul' z c:= by
       classical
       have hv(c:S.Field m):whole T (sole o) (sole c : Labels S (fun _:Unit=>m)) y w= (sectionLabels (d:=Sum.elim (fun _:Unit=>m) e) w (m:=moment T (beside (sole o) y))) (sole c):=sectionLabels_apply .. |>.symm
       have hf(c:S.Field m):sole c= update (β:=fun _:Unit=>S.Field m) 0 () c:=funext (fun i=>by cases i; exact (show update (β:=fun _:Unit=>S.Field m) 0 () c ()=c from Function.update_self (β:=fun _:Unit=>S.Field m) () c 0).symm)
       rw [hv,hv]; simp_rw [hf]; apply MultilinearMap.map_update_smul
lemma upon_observe (m:ℕ){o:E4}{y:J→E4}(w:Labels S e)(h:T.Hierarchy)(hr:T.respects S)(hv:Injective (beside (sole o) y)):upon T m o y w= observeOne S T o y (names w) m:=by
    apply LinearMap.ext; intro f; change whole T _ _ _ _ = _
    rw [whole_observed]; change observe T _ (beside (sole (⟨m,S.representative m f⟩:L.Token)) _)=_
    rw [← projectedOne T _ m _ h.laws.toSymmetric hr hv,S.rep]

def shadowOld {Q:DiffPlan S}(P:Prescription Q)(n:ℕ)(x:I→ E4)(o:E4)(v:Labels S d): S.Field n:=shadow P n x (names v) o

def discrepancy (T:Table L)(m:ℕ)(x:I→E4)(o:E4)(v:Labels S d)(c:S.Field m)(y:J→E4)(w:Labels S e):ℂ:=whole T x v y w - upon T m o y w c
lemma discrepancy_old (P:Prescription Q)(m:ℕ)(x:I→E4)(o:E4)(v:Labels S d)(y:J→E4)(w:Labels S e) (hT:T.Hierarchy)(hS:T.respects S)(hI:Q.Inclusions T)(he:Injective (beside (sole o) y)):discrepancy T m x o v (shadowOld P m x o v) y w=observe T (beside x y) (beside (names v) (names w)) - P.truncated T m x (names v) o y (names w):=by
    rw [discrepancy,whole_observed,shadowOld,upon_observe _ _ hT hS he,compatible_shadows] -- arg order via rw many prop goals
    all_goals assumption

def expo (i:Exterior L): Fin i.n → ℕ:=fun j=>(i.letter j).fst
def fields (S:Table L)(i:Exterior L): Labels S (expo i):=fun j=>S.project (expo i j) (i.letter j).snd
def swung (i:Exterior L)(k:Ortho)(o:E4): Fin i.n → E4 := fun j=> o + Ortho.move k (bearing i j)
def turnsPort (X:S.Rotation)(k:Ortho)(i:Exterior L) := roll X k (fields S i)

set_option maxHeartbeats 600000 in
private lemma reading_rotate (hX:X.Oriented S){x:I→E4}{k:Ortho}{o:E4}(e:Exterior L)(v:Labels S d)
    (hLaw:X.Laws Q ρ)(hS:S.Hierarchy)(he:Injective (beside (away (Ortho.move k⁻¹ ∘ x) (Ortho.move k⁻¹ o)) (bearing e))): Prescription.reading S (Ortho.move k⁻¹ ∘ x) (names (roll X k⁻¹ v)) (Ortho.move k⁻¹ o) e = whole S x v (swung e k o) (turnsPort X k e):=by
    unfold Prescription.reading; dsimp only; rw [if_pos (by exact he)]; let y:= roll X k⁻¹ v; let p:= fields S e; let z:= Ortho.move k⁻¹ ∘ x
    let Z:=beside (away z (Ortho.move k⁻¹ o)) (bearing e); let E:= whole S (away z (Ortho.move k⁻¹ o)) y (bearing e) p
    have hw: observe S Z (beside (names y) e.letter) = E:=by
       unfold E; rw [whole_observed]
       have hi(q:I⊕Fin e.n): S.classTokens (beside (names y) e.letter q) = S.classTokens (beside (names y) (names p) q) := by
           rcases q with q|q; rfl; simp only [beside_right,names,p,fields,expo]; change (⟨_,S.project _ _⟩:S.Tag)=(⟨_,S.project _ _⟩:S.Tag); erw [S.rep]; rfl
       unfold observe worded; rw [S.readAt,S.readAt,← S.at_project S hS.laws.toSymmetric (fun _=>le_rfl) (runs_conf.mpr he),← S.at_project S hS.laws.toSymmetric (fun _=>le_rfl) (runs_conf.mpr he)]; exact congr_arg (S.useAt S _) (funext (fun q=>hi (runNames (I⊕Fin e.n) q)))
    refine hw.trans (?_); unfold whole; let z':= Ortho.move k ∘ Z; let v':= roll X k (stages y p)
    calc E = moment S z' v' := (roll_observes X k hX he).symm
         _ = moment S (fun i=> z' i + o) v' := ((carrying hS ((Ortho.move_injective _).comp he) o).symm) -- inference
         _ = _ := by
             have ht:(fun i=>z' i + o)=beside x (swung e k o):=by
                 funext i; rcases i with i|i
                 · change Ortho.motion k (Ortho.move k⁻¹ (x i) - Ortho.move k⁻¹ o) + o = _; rw [map_sub]; change Ortho.move k (Ortho.move k⁻¹ (x i))-Ortho.move k (Ortho.move k⁻¹ o) +o = x i; rw [Ortho.move_inv,Ortho.move_inv,sub_add_cancel]
                 exact add_comm _ _
             have hf:v'=stages v (turnsPort X k e):=by
                funext i; cases i with
                | inl i=> change X.act (d i) k (X.act (d i) k⁻¹ (v i))=v i; rw [← hLaw.group,mul_inv_cancel,hLaw.fixes]
                | inr i=>rfl
             exact Eq.trans (congr_arg (fun z:I⊕Fin e.n→ E4=> moment S z v') ht) (congr_arg (fun a:Labels S (Sum.elim d (_:Fin e.n→ℕ))=> moment S (beside x _) a) hf)
lemma discrepancy_spin (P:Prescription Q)(hLaw:X.Laws Q ρ)(hS:S.Hierarchy)(hX:X.Oriented S){x:I→E4}{k:Ortho}{o:E4}{m n:ℕ}(v:Labels S d) (c:S.Field m)
    (h:orbitMargin P n x o):
    spinning P X n x o k v - spinning P X n (sole o) o k (sole c : Labels S (fun _:Unit=>m)) =
    ∑ i∈bands Q n, (∑ e∈(P.sheet i).support,(P.sheet i) e * discrepancy S m x o v c (swung e k o) (turnsPort X k e)) • X.act n k (P.loaded i n):=by
    unfold spinning shadow; simp_rw [map_sum,map_smul]; rw [← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl fun i hi=>?_ ; unfold Prescription.ope; rw [← sub_smul,← Finset.sum_sub_distrib]; apply congr_arg (· • _); refine Finset.sum_congr rfl (fun e he'=> ?_)
    rw [← mul_sub]; unfold discrepancy; apply congr_arg (_ * ·)
    exact congr_arg₂ (·-·) (reading_rotate hX _ _ hLaw hS (h i hi k⁻¹ e he')) (reading_rotate (I:=Unit) (d:=fun _:Unit=>m) hX _ (sole c) hLaw hS (by
       have hh : away (Ortho.move k⁻¹ ∘ sole o) (Ortho.move k⁻¹ o)= sole (0:E4) :=by funext ⟨⟩; exact sub_self _
       rw [hh]; exact bearing_clear e))
end YM.OPE.Orbits
