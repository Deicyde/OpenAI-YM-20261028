import YM.Next.RANK.HomeSync
import YM.Next.RANK.Respire
import YM.Next.RANK.Spaces
import YM.Next.RANK.Spirals

/-!
# Actual untransported polynomial interpretation

Locate initial `Answer` Wick input exactly when $κ(k)$ shift-invariant as
required. Pin matrix and kernel requests. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Ribbon
open Function Filter RG Thirst Baler Lattice Wilson MeasureTheory Relation Corona Value Glyph Marker Perch Vac.Numbers Alarm Station Cells Spindle Atlas Edition Normal LiftMark Rise MvPolynomial
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} {C : Family G} {N k d p D : ℕ} {o : ℝ}
variable {v : C.label d} {n : Side} {b R : ℕ} {ι V W : Type}
lemma coin_rename (P : poly V) (f : V→ W) (h : Injective f) : coin P≤ coin (rename f P):=by
  -- undo via subst sending unknown positions to zero
  let M := fun i : W => if h:∃ j,f j=i then Finsupp.single (Classical.choose h) (1:ℂ) else 0
  have hv i:M (f i)=Finsupp.single i (1:ℂ):=by
    unfold M; split
    · rename_i hp; rw [h (Classical.choose_spec hp)]
    rename_i hp; exact False.elim (hp ⟨i,rfl⟩)
  have hs : (exchange M).comp (rename f)=(AlgHom.id ..) := by ext1 i; rw [AlgHom.comp_apply, rename_X, exchange_x, hv, glyph, Finsupp.linearCombination_single,one_smul]; rfl
  have hp (i):coin (glyph (M i)) ≤ 1:= by
    unfold M; split
    · simp [coin,glyph]
    simp [coin,glyph]
  calc
    _ = coin (exchange M (rename f P)):= by rw [← AlgHom.comp_apply,hs];rfl
    _ ≤ _:= by simpa only [one_pow,mul_one] using rise M 0 zero_le_one (c:=1) le_rfl hp _ le_rfl

lemma call_inj (r : 4*b ≤ R) : Injective (calls (G:=G) r):= by
  rintro ⟨⟨⟨x,i⟩,hi⟩,a⟩ ⟨⟨⟨u,v⟩,hv⟩,b⟩ h
  have he : (x,i,a)=(u,v,b):=Subtype.ext_iff.mp h; cases (congr_arg Prod.fst he); have hp:=congr_arg Prod.snd he; simp at hp; rcases hp with ⟨rfl,rfl⟩; rfl

def raww (C : Family G) (k N p : ℕ) (d : ℕ) (r : 2*(sizeQ C k+1)<(C.side k p).val) (f : C.label d→ poly (Up C k p (sizeQ C k))) (v : C.label d) :=
    sender r (C.path.rep N p k).p.threshold (GaugeScale C k N p) (f v)
lemma chaired (k N p d) (A : Family G) (h : A.Makes) (hk : k≤N) (r : 2*(sizeQ A k+1)< (A.side k p).val) (f) (u):
    luminosity (C:=A) f r (Price.shrink A k N p) u=raww A k N p d r f u := by
  unfold luminosity raww sender; rw [(h.wilson.represents N p k hk).vac]; rfl

section
variable (H : C.Makes) (hk : C.ref d≤k) (hK : k≤ N) {S : Rules G} {b q : ℕ} {a : ℝ}
variable (r : 4*sizeQ C k≤wood C.path.levels k) (p' : Provision C d k N p (scouts C k) (sizeQ C k))
variable {F : C.label d→ₗ[ℂ] poly (Up C k p (sizeQ C k))}
local notation "ϕ" => raww C k N p d p'.length F
local notation "M"=>furnace C F r p'
include H hK

lemma carried (x) : (M) x= rename (calls r) (ϕ x):= by rw [furnace,noteL,chaired _ _ _ _ C H hK]
include hk
lemma framed (ha : 0≤a) (h : ∀ z,WRead S k N p d (sizeQ C k) (scouts C k) D a z (F z)) (x): Spirit (ϕ x) := by
  rw [← chaired _ _ _ _ C H hK]; intro w u
  rw [coarse,coarse]; let t:= Price.shrink C k N p
  rw [show t • coloring u w=coloring u (t • w) from funext fun j=> (G.adjoint u |>.map_smul t (w j)).symm,tinted]; exact (land H hk hK ha h x _ u).symm
omit H hK hk in
lemma qualified (ha : 0≤a) (h : ∀ z,WRead S k N p d (sizeQ C k) (scouts C k) D a z (F z)) (x):totalDegree (ϕ x) ≤ D :=
    (factor_degree ..).trans ((ascent ..).trans (tallied (h x) ha|>.1))
omit hk in
lemma required (z) (hZ : MarkedStart M z D (tin (clim C.path.levels k) D) (GaugeScale C k N p) o N p) (hg : GaugeScale C k N p≤ C.path.levels.clock.threshold k) (x):
    coin (ϕ x) ≤ Perch.bill 1 (clim C.path.levels k)*paid C d k N p x:= by
  have hp : 0<GaugeScale C k N p:=inv_pos.mpr (Real.sqrt_pos.mpr (Overlay.beta_positive H.wilson hK))
  apply (coin_rename _ _ (call_inj r)).trans; rw [← carried H hK r p'];
  apply ((blends (M x) _ (show 1≤ C.path.levels.clock.threshold k/GaugeScale C k N p from (le_div_iff₀ hp).2 (by simpa))).trans ((hZ.2.1 x).2)).trans
  exact mul_le_mul_of_nonneg_right (Glimmer.billed _ ((shaded D).trans (by norm_num))) (paid_pos ..)

-- shape/gauge support in cube
omit H hK hk in
lemma origin0 (P : poly (slotC G b)) (h : Spirit P) (g : ℝ) (o : Site n) : Reliable g G n (Spindle.patch b o) (signet o g P):= by
  let f (U : Config G n):= fun i : slotC G b=> curl b U g o i.1 i.2
  refine ⟨fun t U=>?_,?_,fun U V H=>?_⟩
  · change text (f (Lattice.gauge t U)) P=text (f U) P
    rw [show f (Lattice.gauge t U)=(fun i:slotC G b=>coloring (t o) (curl b U g o) i.1 i.2) by
      ext1 i; unfold f coloring curl; rw [read_gauge, Gauge.curvature_conjugate, _root_.map_smul]]; exact (h (curl b U g o) (t o)).symm
  · have hg i: Continuous fun U : Config G n=> curl b U g o i:= by
      unfold curl; have he:= G.continuous_curvature.comp (read_cont b o i (G:=G)); exact (continuous_const (y:= (g⁻¹:ℝ))).smul (show Continuous fun U : Config G n=> G.curvature (registered b U o i) from he)
    clear h
    apply Continuous.measurable; unfold signet; induction P using MvPolynomial.induction_on with
    | C x=> simp only [text,aeval_C]; exact continuous_const
    | add p q hp hq=> simp only [text, _root_.map_add]; apply Continuous.add <;> assumption
    | mul_X p i hp=> simp only [text,_root_.map_mul,aeval_X]; refine hp.mul (Complex.continuous_ofReal.comp ?_); exact (EuclideanSpace.proj i.2 : G.Color →L[ℝ] ℝ).continuous|>.comp (hg i.1)
  apply congr_arg (fun x=> text x P); funext i; unfold curl; exact congr_arg (fun v=> (g⁻¹ • G.curvature v).ofLp i.2) (reads_face b o i.1 U V H)

end
end YM.Next.Rank.Ribbon
