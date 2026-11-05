import YM.Next.RANK.Alarm
import YM.Next.RANK.Presenter
import YM.Next.RANK.TrueWind


/-!
# Oriented singleton along the FONT to restart

Form actual inserted family for all probes in a row. Compute its quiet and
its individual components from same measurements used in Spindle. Use same
copies and gauge averages, proves nothing yet about higher credentials.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Edition
open Function Filter RG Thirst Lattice Wilson MeasureTheory Marker Value Perch Vac.Numbers Alarm Spindle Station Cells Glyph Atlas
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius

variable {G : Gauge} {F : Family G} {N k i v d p : ℕ} {b : ℝ} {x : Points v}

-- conjugation selector

def dot (k : Prop) (u : ℂ) := if k then star u else u
lemma dot_norm (z u) : ‖dot z u‖=‖u‖:= by unfold dot; split;simp; rfl
lemma dot_move (z : Prop) (t : ℝ) (u : ℂ) : dot z ((t:ℂ)*u)= (t:ℂ)*dot z u:= by unfold dot;split <;> simp [mul_comm]
lemma dot_add (z) (u v : ℂ) : dot z (u+v)=dot z u+dot z v:= by unfold dot;split;exact star_add ..;rfl
lemma dot_meas (z : Prop) : Measurable (dot z):= by unfold dot;split; exact (continuous_star (R:=ℂ)).measurable; exact measurable_id

lemma push_sym (P : Levels G) (k n : ℕ) (F : Config G (P.S.side (k+1) n) →ℂ)
    (h : Integrable F (prior G (P.S.side (k+1) n))) (s : Signed) (x : Site (P.S.side k n)) (b : ℝ) :
    let A:= P.clock.op k n
    A.push b (F∘pull s (A.ratio.embed x))=(A.push b F) ∘ pull s x:= by
  intro A; let T := P.blocks k n; let z:=pull (K:=G.El) s x; let y:=pull (K:=G.El) s (A.ratio.embed x); let m:=prior G (P.S.side (k+1) n)
  ext1 v
  let g (t):= A.density b t (z v) • F t
  have hx : Integrable g m:= StepData.push_slice (P.transition_mass k n b) (z v) F h
  have hg := integral_map (prior_pull (G:=G) s (A.ratio.embed x)).aemeasurable (μ:=m) (f:=g)
    (by rw [MeasurePreserving.map_eq (prior_pull ..)]; exact hx.aestronglyMeasurable)
  rw [(prior_pull ..).map_eq] at hg
  change (∫ u, A.density b u v • _ ∂m)=∫ u,g u ∂m
  apply Eq.trans _ hg.symm; apply integral_congr_ae; filter_upwards with t
  unfold g; rw [T.symmetric b t v s x]; rfl

-- $μ$ axis consistency for *any* rolled price at the course

lemma flow_sym {C : Family G} (A : Course C N p k) (F : Config G (C.side N p) →ℂ) (h : Integrable F (prior G _))
    (s : Signed) (j : ℕ) (hm : j≤N) (x : Site (C.side j p)) :
    A.flow (F∘pull s ((C.S.toDepth hm p).embed x)) j hm=(A.flow F j hm)∘pull s x:= by
  induction hm using Nat.decreasingInduction with
  | self => rw [A.flow_self,A.flow_self]; rw [show (C.S.toDepth _ p).embed x=x from ?_]
            unfold Ratio.embed
            rw [show (C.S.toDepth (m:=N) (N:=N) le_rfl p).count.val= 1 from Nat.eq_of_mul_eq_mul_left (C.side N p).property (by rw [mul_one]; exact (C.S.toDepth (Nat.le_refl N) p |>.exact_size).symm)]
            rw [one_smul,wrap_lift]
  | of_succ i hi IH =>
    rw [A.flow_step _ i hi,A.flow_step _ i hi,embed_comp (a:=(C.path.levels.clock.op i p).ratio) (b:=C.S.toDepth hi p),IH]; exact push_sym C.path.levels i p _ (A.flow_int F h (i+1) hi) _ x _
lemma flow_dot {C : Family G} (A : Course C N p k) (F : Config G (C.side N p) →ℂ) (h : Integrable F (prior G _)) (m : ℕ) (hm : m≤N) (p' : Prop):
    A.flow (dot p'∘F) m hm=dot p'∘ A.flow F m hm:= by unfold dot;split;exact Spindle.flows_star C A F h m hm;rfl

-- actual bill, all fields and markers. T width cell set depends ONLY on p.

variable (C : Family G) (b : ℝ) (x : Points v) (hN : k ≤ N) (p : ℕ)

def origin (k N p : ℕ) (v : Fin v→ C.label d):= Ship.clients C (asked v) b k N p x

def Issued (v : Fin v→ C.label d) := Array.stamp (Ship.yard C b hN p) (C.beta N p)
    (Read.bareP (origin C b x k N p v))
-- Note remove h

abbrev Listens := (Ship.yard C b hN p).Cell × Fin v

def fp (m : Listens C b (v:=v) hN p) := (Ship.yard C b hN p).hand m.1
def hand (m : Listens C b (v:=v) hN p) := (Ship.yard C b hN p).omega m.1

def seats : Listens C b (v:=v) hN p→ Site (C.side k p) := Peak.readers (C:=C) x hN hN

lemma stamp_single (s : Fin v→ C.label d) (i : Listens C b (v:=v) hN p) :
    (fun U=> (Issued C b x hN p s U).part (Glyph.slot i))= dot (fp C b hN p i)∘ Spindle.singleP C N p (s i.2) ∘ pull
      (hand C b hN p i) ((C.S.toDepth hN p).embed (seats C b x hN p i)) := by
  ext1 z
  let T:= Ship.yard C b hN p; let a:= fp C b hN p i; let V:= pull (T.omega i.1) (T.translateBy i.1) z
  rw [Issued,Array.stamp_part]
  have he : ∀ j : T.Cell,j≠i.1→ fibre j (Glyph.slot i)=Glyph.quiet _ := by
    intro j hj; apply Subtype.ext; ext m; simp [fibre, scene, Glyph.slot, Census.quiet, Census.fire];exact fun h=> hj (congr_arg Prod.fst h)
  rw [Finset.prod_eq_single i.1]; rotate_left
  · intro j _ hj
    rw [he j hj]; unfold Tiling.copy; split<;> simp [Read.bareP]
  · simp
  have hh : fibre i.1 (slot i)= slot i.2:= by apply Subtype.ext; ext m;rw [fibre_mem]; cases i; simp [slot,Census.fire]
  rw [hh]
  have hp (u:Config G (C.side N p)): (Read.bareP (origin C b x k N p s) u).part (slot i.2)=origin C b x k N p s i.2 u:= by simp [Read.bareP,Glyph.expand,slot,Census.fire]
  let v:= bare (C.beta N p) z
  change (v:ℂ) * T.copy _ _ _= _
  let δ:= T.omega i.1; let c :=T.translateBy i.1
  let f:= C.O N p (s i.2); let y:=location C.S k N p (Station.choose C.path.levels b k x i.2)
  have hq : (C.S.toDepth hN p).embed (seats C b x hN p i)= affine δ c y:= by
    unfold seats Peak.readers; rw [exact_camp]; simp only [ancestor, Ratio.embed_parent]; exact (exact_camp C b x p hN i).symm
  unfold Tiling.copy
  simp_rw [hp]; rw [Function.comp_apply,Function.comp_apply,hq]
  let pp:= affine δ c y
  let B:= bare (n:=C.side N p) (G:=G) (C.beta N p)
  have hx:C.O N p (s i.2) 0 (pull δ pp z)=f y (pull δ c z):= by
    rw [show pull δ pp z=pull 1 y (pull δ c z) by rw [pull_pull,mul_one],pull_one]
    rw [C.translation,zero_add]
  dsimp only [Spindle.singleP]; rw [bare_pull (C.beta N p) z]
  rw [show C.O N p (s i.2) 0 _=_ from (show C.O N p (s i.2) 0 (pull (hand C b hN p i) (affine δ c y) z)=_ from hx),dot_move]; congr 1

def puller (i : Listens C b (v:=v) hN p) := pull (K:=G.El) (hand C b hN p i) (seats C b x hN p i)
def Bills (s : Fin v→C.label d) (h : Course C N p k) := h.flow (Issued C b x hN p s) k hN

lemma origin_int (s : Fin v→C.label d) (i) : Continuous fun z => (Read.bareP (origin C b x k N p s) z).part i:= by
  simp_rw [Read.bareP,Glyph.expand]
  apply continuous_finsetProd _ fun j _=> C.continuousO _ _ _ _ _

lemma s_quiet (h : Course C N p k) (H : C.Makes) (s : Fin v→ C.label d) :
    (fun V => (Bills C b x hN p s h V).part (quiet _))=fun V => ((C.path.rep N p k).eval V:ℂ) := by
  refine Eq.trans (Array.flow_vac h hN _ (X:= Read.bareP (origin C b x k N p s)) (origin_int C b x (k:=k) (N:=N) p s) (fun _=> Glyph.raw_part _)) ?_
  rw [h.vacuum_at H k hN le_rfl]

lemma s_single (h : Course C N p k) (H : C.Makes) (s : Fin v→ C.label d) (hp : C.ref d≤ k) (i : Listens C b (v:=v) hN p) :
    (fun V => (Bills C b x hN p s h V).part (slot i)) = dot (fp C b hN p i)∘ (
       pinHat C d k • (parcel C d k N p (s i.2)).density 0 (C.localSection d) (C.path.rep N p k)) ∘ puller C b x hN p i:= by
  let B := Issued C b x hN p s
  have hB : Integrable B (prior G (C.side N p)):= (Array.stamped_cont _ _ (origin_int C b x (k:=k) (N:=N) p s)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let Q := (Poly.get (R:=Stock.census (Listens C b (v:=v) hN p)) (Glyph.slot i)).restrictScalars ℝ
  let v:= s i.2; let δ:=hand C b hN p i; let Y:= Spindle.singleP C N p v
  let L:= seats C b x hN p i; let Z:=pull (K:=G.El) δ ((C.S.toDepth hN p).embed L)
  have hY := Spindle.singleP_int C N p v
  refine (Course.flow_linear h B Q hB k hN).trans ?_
  rw [show Q ∘ B= _ from stamp_single C b x hN p s i, Spindle.rates_arc (C:=C) (h:=H) (h₁:=hp) h _ _ hN le_rfl]
  change h.flow (dot _ ∘ Y ∘ Z) k hN=dot _ ∘ (h.flow Y k hN) ∘ _
  have he : Integrable (Y ∘ Z) (prior G (C.side N p)):= (MeasurePreserving.integrable_comp (show MeasurePreserving Z (prior G (C.side N p)) (prior G (C.side N p)) from prior_pull ..) hY.aestronglyMeasurable).mpr hY
  rw [flow_dot h _ he]; unfold Z; rw [flow_sym h Y hY δ]; rfl

end YM.Next.Rank.Edition
