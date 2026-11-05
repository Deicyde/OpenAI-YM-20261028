import YM.UVExtension.Projection.Lodge

/-! Convert the actual real wave price, and use harmonic normalization for uniqueness. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Projection
open Lattice RG Precision Tree Exterior Bloch Laurent Wilson Stationary Filter Function Finset
open scoped Matrix Topology BigOperators ContDiff Classical
variable {G : Gauge} {m: Side}

abbrev HatWave (G : Gauge) := TypeFace 1 → G.ColorIndex → ℂ
def ValidPitch (a: HatWave G):= ∀ x y, ‖a x y‖ ≤1

def paint (z : Loc G 1)(a : ℂ): HatWave G:= Function.curry (Pi.single z a)
lemma paint_clear (z:Loc G 1)(a:ℂ)(h:‖a‖≤1):ValidPitch (paint z a):=by
  intro x y; unfold paint Function.curry; by_cases H : (x,y)=z <;> simp [H,h]
lemma pigment (p : Site m)(i : Loc G 1) : relay p i= axes (pew p (paint i 1))+Complex.I • axes (pew p (paint i (-Complex.I))):=by
  ext1 ⟨x,y,z⟩; change cell p x*(Pi.single i (1:ℂ): Loc G 1→ℂ) (y,z)=
    ↑((cell p x * paint i 1 y z).re)+Complex.I* ↑((cell p x*paint i (-Complex.I) y z).re)
  by_cases he : (y,z)=i <;> simp [paint,he]; apply Complex.ext <;> simp
lemma rhyme {U : Link G m→ℝ}{ε : ℝ} (hp : ∀ (i j:Site m) (u v:HatWave G), ValidPitch u → ValidPitch v →
    ‖iteratedFDeriv ℝ 2 U 0 ![pew i u,pew j v]‖ ≤ ε): Recorded (0:Picture G 1) U (4*ε) := by
  intro p i b
  let r j:= (b j,i j); let ψ: Fin 2→ℂ:= ![1, -Complex.I]; let D:Fin 2→ℂ:=![1,Complex.I]
  let f (j k: Fin 2):= pew (p j) (paint (r j) (ψ k))
  let g (j k: Fin 2):= D k • axes (f j k)
  let A:= noteAt U 2
  have ht j: ‖ψ j‖ ≤1:=by fin_cases j <;> simp [ψ]
  have hg : ‖A (glyph p i b)‖ ≤ 4*ε := by
    rw [show glyph p i b=(fun i=> ∑ j,g i j) from funext (fun j=> by
      rw [Fin.sum_univ_two]; change relay (p j) (r j)=_; rw [pigment (p j) (r j)] -- change lhs
      simp [g,f,ψ,D]), MultilinearMap.map_sum (g:=g)]
    refine (norm_sum_le ..).trans ((sum_le_sum (g:=fun _=> ε) fun q _=> ?_).trans_eq (by simp))
    rw [show A _= _ from A.map_smul_univ (fun i=> D (q i)) (fun i=> axes (f i (q i))), norm_smul]
    have he k: ‖D k‖=1:=by fin_cases k <;> simp [D]
    simp_rw [norm_prod,he,prod_const_one,one_mul]
    change ‖A (axes∘(fun i:Fin 2=> f i (q i)))‖≤_
    unfold A; rw [note_real,Complex.norm_real,Tensor.coeff,_root_.smul_apply,norm_smul]
    let u:=f 0 (q 0); let v:= f 1 (q 1)
    rw [show (fun i=> f i (q i))= ![u,v] from funext fun i => by fin_cases i <;> rfl]
    have hu : ‖iteratedFDeriv ℝ 2 U 0 ![u,v]‖ ≤ ε:= hp _ _ _ _ (paint_clear _ _ (ht _)) (paint_clear _ _ (ht _))
    exact (mul_le_of_le_one_left (norm_nonneg _) (by norm_num [Nat.factorial])).trans hu
  have ht: collected (0:Picture G 1) p i b=0:=by unfold collected; split <;> simp
  rw [ht,sub_zero]; exact hg

lemma hear_price {m:ℕ→Side}(U:∀ i, Link G (m i)→ℝ)(K:Picture G 1)(h : Tendsto (fun i=> (m i).val) atTop atTop) (ε:ℕ→ℝ)(he: Tendsto ε atTop (𝓝 0))
    {s K' : ℝ}(hp:0<s)(hk:∀ i b,Firm s K' (K i b))(hv:∀ i, Recorded K (U i) 0)(hu : ∀ i, Recorded (0:Picture G 1) (U i) (cents (m i)*ε i)):
    (∀ i j (p:Corn (Keys 1)),K i j (axes p)=0) ∧ ∀ i,iteratedFDeriv ℝ 2 (U i) 0=0:=by
  have hy x y (v:Corn (Keys 1)): K x y (axes v)=0:=by
    obtain ⟨p,u,H,A⟩:= fleet m h (axes v) (axes_real v)
    exact tendsto_nhds_unique (harvest hk (ε:=0) (fun i=> by simpa using hv i) tendsto_const_nhds v p u H A x y) (harvest (fun i b=> Firm.zero hp) hu he v p u H A x y)
  refine ⟨hy,fun i=>?_⟩
  have hz : aperture 0 (U i) (fun _=> 0) 1:=by
    intro p a b g; unfold g; rw [(record_exact ..).1 (hv i)]; unfold collected
    have hg : noteAt (fun _:Link G (m i)=>0) 2=0:=by unfold noteAt beat; simp [enlarge,recording]; ext; simp -- revise
    split
    · have hh: K a b (outphase p)=0:= by
        rw [← axes_of_real (out_real p),hy]
      rw [hh,mul_zero,hg]; simp
    rw [hg]; simp
  rw [aperture_eq hz]; simp
end YM.UVExtension.Projection
