import YM.UVExtension.Beach.Carts
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Beach
open Function Filter Set Metric Lattice RG Wilson
open Extraction Fallow Poppy Tide Swell Lamppost Spire Pier Rafter
open scoped Topology BigOperators Classical ContDiff
variable {n j N m:ℕ} (S:Schedule)
local notation "X"=> Tabletop n
local notation "D"=> Points n
variable {A:Set (Points n)}(h:IsOpen A){a b:ℝ}(ha:0<a)
   (F:ℕ→Row a→ Tabletop n→ℂ) (p:ℕ)
set_option quotPrecheck false
local notation "T"=> desk a ha
local notation "V"=> Row a
-- abstraction for any mesh arrays
variable (L:List (Axel n))
def zoom (N p:ℕ)(j:ℕ)(h:j≤N)(x:Tabletop n) (v:Row a):= rake (S.a j) (F N v∘ scoop S p h) L x
def round (N p:ℕ)(j:ℕ)(h:j ≤ N)(x:Tabletop n) (v:Row a):= zoom S F L N p j h (Extraction.address (S.a j) (Extraction.tag (S.a N) x)) v
structure Patio (S:Schedule)(a b:ℝ)(ha:0 < a)(F:ℕ→ Row a→ Tabletop n→ℂ)(p:ℕ)(A:Set (Points n)):Prop where
    prices :∀ᶠ j in atTop,∀ N (h:j≤N) (x:Tabletop n),Extraction.tag (S.a j) x∈ A→ Sail (desk a ha) (fun d:Row a=>F N d (scoop S p h x)) (expS S b j)
variable (hh:Patio S a b ha F p A) (K:Set (Points n))(hk:IsCompact K)(hK:K⊆ A)
include hh
-- poly coarse at A_j nearest to x∈K raises.D.SpaceA complex.y.C.f.Member.
private def money (b:ℝ)(t i:ℕ):= expS S b i*(2*(S.a i)⁻¹)^t -- b implicit unused
local notation "ψ"=> fun j=>expS S b j
lemma tall (hl:L.length ≤ m) : ∀ᶠ j in atTop,∀ N (hN:j≤N)(x:X), (∀ y:X,dist (tag (S.a j) y) (tag (S.a j) x) ≤ L.length*S.a j→ tag (S.a j) y∈A)→ Sail (desk a ha) (zoom S F L N p j hN x) (money (b:=b) S L.length j):= by
    induction L with
    | nil=>
       filter_upwards [hh.prices] with j hj N hN x hx; exact (hj _ hN x (hx x (by simp))).mono (by simp [money])
    | cons i l ih=>
       filter_upwards [ih (by simp at hl; omega)] with j hj N hN x hv
       let V' (y):= zoom S F l N p j hN y; let u:= S.a j; have hu:=S.a_pos j
       have he(y:X)(h: dist (tag u y) (tag u x)≤ u): Sail T (V' y) (money (b:=b) S l.length j):= hj _ hN y (fun z hz=> hv z ((dist_triangle _ (tag u y) _).trans ((add_le_add hz h).trans_eq (by simp [u,add_mul]))))
       have hX : dist (tag u (x+hike i)) (tag u x) ≤ u := by simpa using! (lengthP (x:=x) hu i 1).le
       let h:= he (x+hike i) hX; exact (((h.sub (he x (by rw [dist_self]; exact hu.le))).scales (u:ℂ)⁻¹)).mono (le_of_eq (by rw [norm_inv,Complex.norm_real, Real.norm_of_nonneg hu.le]; unfold money; rw [List.length_cons,pow_succ]; ring))
include h hk hK in
private lemma patches (l:ℝ) : ∀ᶠ j in atTop,∀ N≥j,∀ x:X, tag (S.a N) x∈ K→∀ y:X, dist (tag (S.a j) y) (tag (S.a j) (Extraction.address (S.a j) (Extraction.tag (S.a N) x)))≤ l*S.a j → tag (S.a j) y∈A:=by
    obtain ⟨r,hr,hR⟩:= hk.exists_cthickening_subset_open h hK; let D':= l+4*n; have he : Tendsto (fun j=>D'*S.a j) atTop (𝓝 0):=by simpa only [mul_zero] using S.shrinks.const_mul D'
    filter_upwards [he.eventually (ge_mem_nhds hr)] with j hj N hv x hx y hy; apply hR; apply mem_cthickening_of_dist_le _ _ _ _ hx; have hm:= (dist_triangle _ _ _).trans (add_le_add hy (approximate (S.a_pos j) _)); refine hm.trans ((Eq.trans_le ?_ hj)); unfold D'; ring -- triangle metas
include hh h hk hK
lemma rocky (hl:L.length ≤ m)(i':ℕ)(z:ℝ)(hv:0<z) (hw:∀ᶠ i in atTop,money (b:=b) S m i ≤ expS S z i):∀ᶠ j in atTop,∀ N (hx:j ≤ N)(x:X), tag (S.a N) x∈K→ Sail T (round S F L N p j hx x) (expS S z j):=by
    filter_upwards [patches S h ha F p hh K hk hK (L.length),tall S ha F p L hh hl,hw] with j hj hp h N hx x hX; refine (hp N hx _ (hj N hx x hX)).mono (le_trans ?_ h); unfold money; apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le; apply pow_le_pow_right₀ _ hl; refine one_le_two.trans (le_mul_of_one_le_right zero_le_two ((one_le_inv₀ (S.a_pos _)).2 ((S.strictAnti.antitone (Nat.zero_le j)).trans_eq S.a_zero))) -- price at m implicit.A
omit h hk hK in
lemma charge (m:ℕ) : ∃ z:ℝ,0<z∧∀ᶠ j in atTop,money (b:=b) S m j ≤expS S z j:=by
    obtain ⟨z,hz,hX⟩:=(PolyB.fromNote (YM.MergeProof.Ribbons.Note.bell_exp S b)).mul (((PolyB.const S 2).mul (PolyB.inverse S)).pow m); exact ⟨z,hz,hX.mono fun i hi=> (le_abs_self _).trans hi⟩
end YM.UVExtension.Beach
