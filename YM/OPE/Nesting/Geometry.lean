import YM.OPE.Nesting.Weights

/-!
# Admissible physical relative geometries

Positive sibling spacing and a uniform sufficiently small upper bound on
all child/parent scale ratios imply the needed positive clearance across even
the deepest subpositions. There is no *lower* bound besides strict positivity
of the declarations. Unary nodes, including those whose center coincides with
the child's point, need no branch factor for that spacing.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Nesting.Tree
open Orbits Orbits.Reader Function Filter Extraction Set Table Measures Menu Atom MeasureTheory Finset
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical


/-- Positive radii bounded recursively by immediate parent scale times β
(except root, bounded by h itself). For `β=1` all nested scales ≤h. -/
def Tapered : (t:Tree) → ℝ → ℝ→ (t.Inner→ℝ)→Prop
 | bud,_,_,_=> True
 | fork n f,h,β,s=> 0 < s (.inl ()) ∧ s (.inl ()) ≤ h ∧ ∀ i, Tapered (f i) (s (.inl ()) * β) β (childAge i s)

def Immediate(M η:ℝ) : (t:Tree) → (t.Inner→ℝ) → (t.Positions→E4)→Prop
 | bud,_,_=>True
 | fork n f,s,z=>let x:Fin n→E4:=fun i:Fin n=>childPlace i z ((f i).topSeat);
   (∀ i, ‖x i-z (fork n f|>.topSeat)‖ ≤ M*s (.inl ())) ∧ (∀ i j,i≠j→η*s (.inl ()) ≤ ‖x i-x j‖) ∧
        ∀ i, Immediate M η (f i) (childAge i s) (childPlace i z)

def current : (t:Tree)→(t.Inner→ℝ)→ ℝ | bud,_=>0 | fork n f,s=>s (.inl ())

variable {t:Tree}{s:t.Inner→ℝ}{z:t.Positions→E4}{α β r r' M M' η η':ℝ}
lemma Tapered.mono (h:t.Tapered r α s)(ha:α≤β)(hr:r≤r'): t.Tapered r' β s :=by
    induction t generalizing r r' with
    | bud=>exact True.intro
    | fork n f ih=>exact ⟨h.1,h.2.1.trans hr,fun i=> ih i (h.2.2 i) (mul_le_mul_of_nonneg_left ha h.1.le)⟩

lemma Tapered.positive (h:t.Tapered r α s)(v:t.Inner):0<s v:=by induction t generalizing r with
 | bud=> cases v
 | fork n f ih=> rcases v with ⟨⟩|⟨i,p⟩; exact h.1; exact ih i (h.2.2 i) ..
lemma Tapered.within (h:t.Tapered r α s)(hα:α≤1)(v:t.Inner): s v ≤ r:=by induction t generalizing r with
 | bud=>cases v
 | fork n f ih => rcases v with u | ⟨j,p⟩
                  · cases u; exact h.2.1
                  exact le_trans (ih j (h.2.2 j) p) (by exact (mul_le_mul_of_nonneg_left hα h.1.le).trans (le_trans (mul_one (s (Sum.inl ()))|>.le) h.2.1))

lemma Relative.mono (h:t.Tapered r α s)(he:Relative M η t s z)(hm:M≤M')(hm':η'≤η):Relative M' η' t s z:=by induction t generalizing r with
 | bud=> exact True.intro
 | fork n f ih => exact ⟨fun j=>(he.1 j).trans (mul_le_mul_of_nonneg_right hm h.1.le),fun i j q p hu=> (mul_le_mul_of_nonneg_right hm' h.1.le).trans (he.2.1 i j q p hu), fun i=> ih i (h.2.2 i) (he.2.2 i)⟩
lemma Tapered.on_boundary(h:t.Tapered r α s)(hm:0≤r): 0≤t.current s∧ t.current s ≤ r :=by cases t with
 | bud=>exact ⟨le_rfl,hm⟩
 | fork=>exact ⟨h.1.le,h.2.1⟩
lemma Relative.from_current(he:Relative M η t s z)(j:t.Positions): ‖z j-z t.topSeat‖ ≤ M*(t.current s):=by cases t with
   | bud=>change Unit at j; cases j; change ‖z ()- z ()‖ ≤ M*Tree.bud.current s; rw [(show z _ - z _ =0 from sub_self _),norm_zero,(show M*Tree.bud.current s=0 from mul_zero _) ]
   | fork=>exact he.1 j

private lemma fourpoint (p q r s:E4): ‖p-q‖ ≤ ‖r-p‖ + ‖r-s‖+‖s-q‖:=by
     rw [norm_sub_rev r p]; exact (c_dist_point p s q).trans (add_le_add (c_dist_point p r s) (le_refl _))

lemma of_immediate (t:Tree) (M η:ℝ)(hM:0≤M)(he:0 < η):∃ C β:ℝ,0 ≤ C ∧ β ∈ Set.Ioc (0:ℝ) 1 ∧ ∀ (s:t.Inner→ℝ)(z:t.Positions→E4)(r:ℝ), t.Tapered r β s→Immediate M η t s z → Relative C (η/2) t s z:=by
    induction t with
    | bud=>exact ⟨0,1,le_rfl,⟨zero_lt_one,le_rfl⟩,fun _ _ _ _ _=> True.intro⟩
    | fork n f ih=>
        choose C b hC hb hf using ih
        let C':ℝ := ∑ i:Fin n,C i; let B:=Insert.insert (min 1 (η/(4*(C'+1)))) (Finset.univ.image b); let β:=B.min' (insert_nonempty ..)
        have h_i(i):C i ≤ C':=single_le_sum (fun j _=>hC j) (mem_univ i)
        have he':0≤C':=sum_nonneg (fun i _=>hC ..)
        have hc':0<C'+1:=by linarith only [he']
        have hb': 0<β := (lt_min'_iff ..).2 (fun v hv=>by
          change v∈(insert (min 1 (η/(4*(C'+1)))) (Finset.univ.image b) : Finset ℝ) at hv; rw [Finset.mem_insert] at hv; obtain rfl|hv':=hv; exact (lt_min zero_lt_one (div_pos he (by linarith only [he']))) ; obtain ⟨i,hi,rfl⟩:=mem_image.mp hv'; exact (hb i).1)
        have hx:β ≤ min 1 (η/(4*(C'+1))):=min'_le _ _ (mem_insert_self ..)
        have hx':β ≤ 1:=hx.trans (min_le_left ..)
        have hb'' :4*(C'*β) ≤ η:=by
           calc 4*(C'*β) ≤ β*(4*(C'+1)) := by linarith only [hb']
                  _ ≤ _ := (le_div_iff₀ (by nlinarith only [hc'])).mp (hx.trans (min_le_right ..))
        have h_i'(i):β ≤ b i:=min'_le _ _ (mem_insert_of_mem (mem_image_of_mem _ (mem_univ _)))
        refine ⟨C'+M,β,add_nonneg he' hM,⟨hb',hx'⟩,fun s z R h hp=>?_ ⟩
        let r:E4:=z (fork n f|>.topSeat); let x(i:Fin n) (v:(f i).Positions) := childPlace i z v; let q(i:Fin n):= x i ((f i).topSeat); let m(i:Fin n):=(f i).current (childAge i s)
        let w:=s (Sum.inl ())
        have hv(i:Fin n):= hf i (childAge i s) (x i) (w*β) ((h.2.2 i).mono (h_i' i) le_rfl) (hp.2.2 i)
        have hv'(i)(v): ‖x i v - q i‖ ≤ C'*(w*β) :=
             ((hv i).from_current v).trans (by
                 obtain ⟨h₁,h₂⟩:=(h.2.2 i).on_boundary (mul_pos h.1 hb').le
                 exact mul_le_mul (h_i i) h₂ h₁ he')
        have h₀:0<w:=h.1
        refine ⟨?_,?_,fun i=>(hv i).mono (h.2.2 i) ((h_i i).trans (by linarith only [hM])) le_rfl⟩
        · rintro (u|⟨i,p⟩)
          · cases u; change ‖z (Sum.inl ())-z (Sum.inl ())‖≤(C'+M)*w; rw [sub_self,norm_zero]; exact mul_nonneg (add_nonneg he' hM) h₀.le
          exact (c_dist_point (x i p) (q i) r).trans ((add_le_add ((hv' i p).trans (by change C'*(w*β) ≤ C'*w; exact mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_left hx' h₀.le).trans_eq (mul_one _)) he')) (hp.1 i)).trans (add_mul ..).symm.le)
        intro i j p m hij
        change (η/2)*w ≤ ‖x i p-x j m‖
        have h_dist:η*w ≤ ‖q i-q j‖:=hp.2.1 i j hij
        calc _ ≤ η*w-(C'*(w*β)+C'*(w*β)) := by nlinarith only [hb'',h₀]
             _ ≤ ‖x i p-x j m‖:=by linarith only [fourpoint (q i) (q j) (x i p) (x j m),hv' i p,hv' j m,h_dist]
end YM.OPE.Nesting.Tree
