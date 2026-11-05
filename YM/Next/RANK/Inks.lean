import YM.Next.RANK.Motor
import YM.Next.RANK.Rails
import YM.Next.RANK.ValueVeneer


/-!
# Real oriented receipt from the actual L

Before allocating Heat. Need the kernel part of Stamped (reality, Ad invariant
real covariances) physically also at all shifts or rotations where used later.
Pin cost at origin on actual Step path.C. Color proof does not impose H equivariant
choice of calibration (such variants including between offsets may be needed outside
Rank widths; not licensed by this test). -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Spindle
open Function Set Filter Lattice Wilson RG Extraction Source Labels Source.Drops Normal Rise Perch Glimmer Station Price
  Configuration Atlas Beamer LiftMark Tariffs MvPolynomial Asymptotics MeasureTheory
open scoped Classical Topology BigOperators Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} {C : Family G} {N p k d b R : ℕ} {o : Site (C.side k p)}
variable {V A : Type*}

def printed0 (r : 4*b ≤ R) (d) (P : poly (slotC G b)) := exchange (ink d (Subtype.val : trimV R G → _)) (rename (calls r) P)

def paper (G : Gauge) (u : G.El) (b) (i : slotC G b) : slotC G b →₀ ℂ := ∑ j : G.ColorIndex,
    Finsupp.single (i.1,j) (↑(G.adjoint u (EuclideanSpace.basisFun _ ℝ j) i.2))

lemma salute (x : Turn b→G.Color) (u : G.El) (p : poly (slotC G b)) :
    text (fun i : slotC G b=> (coloring u x i.1) i.2) p=text (fun i : slotC G b=>x i.1 i.2) (exchange (paper G u b) p) := by
  apply DFunLike.congr_fun (g:= (aeval (R:=ℂ) _).comp (exchange (paper G u b))); ext1 i; simp only [aeval_X,AlgHom.comp_apply, exchange_x, glyph, paper,_root_.map_sum,Finsupp.linearCombination_single,_root_.map_smul,aeval_X]
  unfold coloring
  let B:= (EuclideanSpace.basisFun G.ColorIndex ℝ).toBasis
  have he : x i.1=∑ j,B.repr (x i.1) j • B j := (B.sum_repr _).symm
  have hv j : B.repr (x i.1) j=x i.1 j := by dsimp only [B];simp
  conv_lhs => rw [he,_root_.map_sum]
  simp_rw [map_smul]
  rw [show ∀ g : G.ColorIndex → G.Color,(∑ i,g i).ofLp i.2=∑ j,(g j).ofLp i.2 from fun g => map_sum (EuclideanSpace.proj i.2 : G.Color →L[ℝ] ℝ) g _,Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun j _=> ?_; rw [hv]; change ((↑( (x i.1 j:ℝ)*((G.adjoint u) (B j)) i.2 ):ℂ))= _; rw [Complex.ofReal_mul]; exact mul_comm ..

lemma tinted (x : Turn b → G.Color) (u : G.El) {n : Side} (h : 2*(b+1)<n.val) {o : Site n} (s : ℝ) :
    rows (o:=o) s h (coloring u x)=coloring u (rows (o:=o) s h x) := by
  have hp (l : Word b):stage l (coloring u x)=G.adjoint u (stage l x) := by
    induction l with
    | nil => exact (map_zero _).symm
    | cons a p H =>
      simp_rw [stage,List.map_cons,List.sum_cons,map_add]; split
      · rw [map_neg]; exact congr_arg (- G.adjoint u _ + ·) H
      exact congr_arg (G.adjoint u _ + ·) H
  funext i; change s⁻¹ • stage _ (coloring u x)= G.adjoint u (s⁻¹ • _); rw [hp,map_smul]
lemma sold_factor (s : ℝ) (F : A→ℝ) (P : poly A) : text F (factors (s:ℂ) P)=text (s • F) P := by
  apply DFunLike.congr_fun (f:= (aeval (R:=ℂ) (fun i=> (F i:ℂ))).comp (factors _)); ext1 i; simp

-- linear atlas stove, raw power $g/t$
def luminosity (F : C.label d→poly (links G (0:Site (C.side k p)) b)) (h : 2*(b+1)< (C.side k p).val) (s : ℝ) (x : C.label d) := factors (↑s:ℂ) (dustAt h (F x))

def Spirit (P : poly (slotC G b)) := ∀ x : Turn b → G.Color, ∀ u : G.El,
    text (fun i : slotC G b=>x i.1 i.2) P = text (fun i : slotC G b=>coloring u x i.1 i.2) P
-- choose needed low Θ kernel properties. quantify at k, not impose solution.
structure Stamped (b R k : ℕ) {P : Schedule} (Y : AtlasData G P p) (r : 4*b≤R) : Prop where
  observes i j : star ((control (k:=k) Y 0 R).cov i j)= (control (k:=k) Y 0 R).cov i j
  orients (u : G.El) :
    let ψ:= scope (fun (i : slotC G b) => Finsupp.single (calls r i) 1) (control (k:=k) Y 0 R)
    scope (paper G u b) ψ=ψ
  -- use elsewhere need `Y.κ(k)` translation-invariant, not at pixel

lemma intact (P : Normal.Symmetric (slotC G b)) {S : poly (slotC G b)} (h : ∀ u : G.El,scope (paper G u b) P=P) (he : Spirit S) : Spirit (milk P S) := by
  have ht (u):exchange (paper G u b) S=S := by
    apply audible; intro s; let A : Turn b → G.Color := fun i=> WithLp.toLp 2 (fun j=>s (i,j))
    exact (salute A u S).symm.trans (he A u).symm
  intro x u; rw [salute]; apply congr_arg
  rw [← show (milk (scope (paper G u b) P) S) = milk P S by rw [h u],← Normal.prepared, ht, h u]

-- Liveness of WM color implies invariant for resulting *radial* Label applying these exact tester rays.
lemma writes_color (r : 4*b ≤ R) (P : poly (slotC G b)) (A : Snap G d) : aeval (kp d A) (printed0 r d P) = text (fun i : slotC G b => lamp d A i.1 i.2) P := by
  apply DFunLike.congr_fun (f:=(aeval (kp d A)).comp ((exchange (ink d Subtype.val)).comp (rename (calls r))))
  ext1 i; simp only [AlgHom.comp_apply,rename_X,exchange_x,glyph,ink,_root_.map_sum,Finsupp.linearCombination_single,map_smul,aeval_X]
  unfold lamp; rw [traffic .., Complex.ofReal_sum]; refine Finset.sum_congr rfl fun j _=>?_; rw [Complex.ofReal_mul, kp_real]; exact mul_comm ..
lemma placed_turn (A : Snap G d) (u : G.El) (p : Turn b) : lamp d (Cast u A) p= G.adjoint u (lamp d A p) := by

  have hp x : access (Cast u A) x=G.adjoint u (access A x) := by
    rw [revealed_cell,revealed_cell,map_sum]; apply Finset.sum_congr rfl; intro i hi
    unfold CellsInt.trail
    simp only [expand,dif_pos (Finset.mem_range.mp hi),Function.comp_apply,Cast]
    unfold CellsInt.east; simp_rw [Taylor.paint_value]
    exact (G.adjoint u).toContinuousLinearMap.intervalIntegral_comp_comm (CellsInt.east_int _ _ ((Tensor.diag_smooth _ 1).continuous))
  unfold lamp oneGlow
  have he (w : Walk) (x : Cover) : Exterior.linkSum (access (Cast u A)) x w=G.adjoint u (Exterior.linkSum (access A) x w) := by
    induction w generalizing x with
    | nil => exact (map_zero _).symm
    | cons a w H=> rw [Exterior.linkSum,Exterior.linkSum,map_add,H]; split <;> simp [*]
  exact he ..

lemma anchored_key (A : Jet G) (u : G.El) : Drops.trunk d (Labels.colored u A)=Cast u (Drops.trunk d A) := rfl

lemma roots_seed (S : poly (slotC G b)) (r : 4*b ≤ R) (d : ℕ) (h : Spirit S) :
    rename (Subtype.val : KeyIn G d → Key G) (trim (printed0 r d S) (key G d) d) ∈ localFields G d := by
  let y:= (printed0 r d S); let p:= trim y (key G d) d
  let f:= (Subtype.val : KeyIn G d → Key G); let X:= rename f p
  constructor
  · have hp : trim X Labels.generation d=X := by
      unfold X; rw [trim_rename]
      have hu : trim p (key G d) d=p := by ext i; simp only [p,trim_coeff]; split_ifs <;>simp
      rw [show generation∘f=key G d from rfl, hu]
    intro i hi
    change Finsupp.weight Labels.generation i≤d
    change i∈X.support at hi
    by_contra H; rw [← hp] at hi; exact (mem_support_iff.mp hi) (trim_coeff .. |>.trans (if_neg H))
  change X ∈ invariantSpace G
  intro J u
  have he (A : Jet G) : Labels.read A X = aeval (kp d (Drops.trunk d A)) p := by
    apply DFunLike.congr_fun (f:=(Labels.read A).comp (rename f)); ext1 i
    have h : i.val.1<d-1 := (spanKey d i).isLt
    simp only [AlgHom.comp_apply, Labels.read,kp,f,Labels.coord,expand, Drops.trunk,dif_pos h,rename_X,aeval_X]
  have hx (A : Snap G d) (u : G.El) : aeval (kp d A) y=aeval (kp d (Cast u A)) y := by
    unfold y; rw [writes_color,writes_color]
    simp_rw [placed_turn A u]; exact h _ u
  have hs : ∀ r : ℝ,flash (Cast u (Drops.trunk d J)) r=Cast u (flash (Drops.trunk d J) r) := by
    intro r; funext i; simp only [flash,Drops.trunk,scaleJet,Cast,expand,dif_pos i.isLt,Taylor.paint, map_smul]
  rw [he,he,anchored_key]; unfold p; rw [← ray_stamp ..,← ray_stamp ..]; apply congr_arg (fun P => evaluate_ray P d)
  funext r; rw [hs]; exact (hx ..).symm

def retro (V : Type*) := @MvPolynomial.map ℂ ℂ V _ _ (starRingEnd _)
lemma escorted (u : V→ℝ) (F : poly V) : text u (retro V F)=star (text u F) := by
  induction F using MvPolynomial.induction_on with
  | C r => simp [text,retro]
  | add p q h1 h2 => simp only [text,map_add] at *; rw [h1,h2,star_add]
  | mul_X p i H =>
    unfold text at *; rw [_root_.map_mul (retro V),map_mul (aeval _),map_mul (aeval _), H]; simp [retro,mul_comm]
lemma flashed (K : Normal.Symmetric V) (hK : ∀ i j, star (K.cov i j)=K.cov i j) (P : poly V) :
    milk K (retro V P)=retro V (milk K P) := by
  have hs i (P : poly V) : slit (K.cov i) (retro V P)=retro V (slit (K.cov i) P) := by
    induction P using MvPolynomial.induction_on with
    | C c => simp [retro]
    | add p q h1 h2 => rw [_root_.map_add,_root_.map_add,h1,h2,_root_.map_add,_root_.map_add]
    | mul_X p j H =>
      rw [mul_comm p,_root_.map_mul (retro V),show retro V (X j)=X j from MvPolynomial.map_X ..,slit_prod,slit_prod, _root_.map_add (retro V), _root_.map_mul (retro V),_root_.map_mul (retro V),H]; simp [retro]; exact Or.inl (hK i j).symm
  induction P using MvPolynomial.induction_on with
  | C r => simp [retro]
  | add p q h1 h2 => rw [_root_.map_add,_root_.map_add,h1,h2,_root_.map_add,_root_.map_add]
  | mul_X p i H =>
    rw [mul_comm p,_root_.map_mul (retro V),show retro V (X i)=X i from MvPolynomial.map_X ..,Normal.feeds,Normal.feeds,H, _root_.map_add, _root_.map_mul (retro V),hs]; simp [retro]
lemma rewound (P : poly (slotC G b)) (r : 4*b ≤ R) (d : ℕ) : printed0 r d (retro _ P) = retro _ (printed0 r d P) := by
  apply audible; intro s
  obtain ⟨A,H⟩ := kp_contains s
  rw [escorted]; unfold text; rw [← H, writes_color,writes_color,escorted]
lemma real_seed (S : poly (slotC G b)) (r : 4*b ≤ R) (d : ℕ) :
    rename (Subtype.val : KeyIn G d → Key G) (trim (printed0 r d (retro _ S)) (key G d) d) = Labels.conjPol
      (rename (Subtype.val : KeyIn G d → Key G) (trim (printed0 r d S) (key G d) d)) := by
  rw [rewound]; let p:= printed0 r d S; let w:= key G d; let f:= (Subtype.val : KeyIn G d → Key G)
  have h : trim (retro _ p) w d = retro _ (trim p w d) := by ext i; simp only [retro,trim_coeff,coeff_map]; split_ifs <;> simp
  rw [h]; simp only [retro, Labels.conjPol, map_rename]; rfl

section
variable (X : AtlasData G C.S p) {Y : Rules G} {e : ℝ}
variable (L : C.label d→ₗ[ℂ] poly (Up C k p b))
variable (h : 2*(b+1) < (C.side k p).val) (r : 4*b ≤ wood C.path.levels k) (t : ℝ)

-- $ξ=g/t$. This stove, no resampling at each occurrence.
def gram : Heater C k d := (rename (calls r)).toLinearMap.comp ((factors (↑t:ℂ)).toLinearMap.comp ((exchange (visit (G:=G) (o:=0) h)).toLinearMap.comp L))
lemma noteL (y) : gram L h r t y=rename (calls r) (luminosity (C:=C) L h t y) := rfl
lemma lit_power (s : C.label d) : totalDegree (gram L h r t s) ≤ totalDegree (L s) := (totalDegree_rename_le ..).trans ((factor_degree ..).trans (ascent ..))
lemma coarse (v : C.label d) (p : Turn b → G.Color) : text (fun i : slotC G b=> (p i.1) i.2) (luminosity (C:=C) L h t v) = text (scan (rows 1 h (t • p))) (L v) := by
  have ht := sold_factor t (fun i : slotC G b=> p i.1 i.2) (dustAt h (L v))
  refine ht.trans ?_
  exact full_dust h (t • p) (L v)

-- Most precise Θ normalization *in actual kernel units*.
theorem caressed (H' : Stamped b (wood C.path.levels k) k X r) {i D : ℕ}
    (H : C.Makes) (hF : C.ref d≤k) (hk : k≤N) (hc : 0≤e) (hL : ∀ v,WRead Y k N p d b i D e v (L v)) (s : C.label d) :
    let F:=C.labels.level d
    ∃ v : C.label d, printed (Wick X (gram L h r t)) s=expose F v ∧ printed (Wick X (gram L h r t)) (star s)=expose F (star v) := by
  intro F
  let v x:= luminosity (C:=C) L h t x
  let K:= control (k:=k) X 0 (wood C.path.levels k)
  let Q:= scope (fun (i : slotC G b) => Finsupp.single (calls r i) 1) K
  let p x:= printed (Wick X (gram L h r t)) x
  let R x:= milk Q (v x)
  have hp x : p x= trim (printed0 r d (R x)) (key G d) d := by
    have he : Wick X (gram L h r t) x= rename (calls r) (milk Q (v x)) := by
      change milk K ((gram L h r t) x)=_; rw [noteL,Normal.labelled]; exact Normal.prepared ..
    change trim (exchange _ _) _ _=_
    rw [he]; rfl
  have hh x : Spirit (R x) := intact Q H'.orients (fun w u => by
    dsimp only [v]; rw [coarse,coarse]
    have he : t • coloring u w=coloring u (t • w) := funext fun a=> ((G.adjoint u).map_smul t (w a)).symm
    rw [he,tinted]; exact (land H hF hk hc hL x _ u).symm)
  have hs x:R (star x)=retro _ (R x) := by
    have he :
      v (star x)=retro _ (v x) := by
      apply audible; intro T; let A : Turn b→ G.Color := fun i=> WithLp.toLp 2 (fun j=>T (i,j))
      rw [escorted]; change text (fun i : slotC G b=> (A i.1) i.2) (luminosity _ _ _ (star x))=star (text (fun i : slotC G b=> (A i.1) i.2) (v x))
      unfold v; rw [coarse,coarse]; exact rays_real H hF hk hc hL x _
    unfold R; rw [he]; apply flashed; intro i j
    dsimp only [Q]; rw [match_name ..]; exact H'.observes ..
  let f := (Subtype.val : KeyIn G d→Key G)
  have ht x : rename f (p x) ∈ localFields G d := by rw [hp]; exact roots_seed (R x) _ d (hh x)
  let T (x) : Label G d := ⟨_,ht x⟩
  have hz x : expose F (F.coords (T x))=p x := by rw [expose_at,F.coords.symm_apply_apply]; apply rename_injective (R:=ℂ) (f:=f) Subtype.val_injective (returns (T x))
  have hQ : T (star s)=Labels.realBar (T s) := by
    apply Subtype.ext; change rename f (p _)= Labels.conjPol (rename f (p s)); rw [hp,hp,hs,real_seed]
  have hv : F.coords (T (star s))=star (F.coords (T s)) := by
    funext i; rw [hQ]; have he:= F.conj_basis (F.coords (T s)) i
    rw [F.coords.symm_apply_apply] at he; exact he
  exact ⟨F.coords (T s),(hz s).symm,(hz (star s)).symm.trans (congr_arg _ hv)⟩
end
end YM.Next.Rank.Spindle
