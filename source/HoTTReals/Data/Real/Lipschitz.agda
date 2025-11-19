module HoTTReals.Data.Real.Lipschitz where

-- liftLipschitz : (f : ℚ → ℝ)
--                 (L : ℚ) (φ : 0 < L) →
--                 Lipschitzℚ f L φ →
--                 (ℝ → ℝ)
-- liftLipschitz f L φ george =
--   recursion
--     {A = ℝ}
--     {B = B}
--     ( liftLipschitzRational , liftLipschitzLimit , ψ , θ , ω , χ , π , ρ )
--   where
--   B : ℝ → ℝ → (ε : ℚ) → 0 < ε → Type ℓ-zero
--   B u v ε ψ = u ∼[ L · ε , ·0< {x = L} {y = ε} φ ψ ] v

--   liftLipschitzRational : ℚ → ℝ
--   liftLipschitzRational = f

--   φ' : ¬ L ≡ 0
--   φ' = ≠-symmetric $ <→≠ φ

--   φ'' : 0 < L [ φ' ]⁻¹
--   φ'' = 0<⁻¹ {x = L} φ

--   foo : (ε : ℚ) → 0 < ε → 0 < ε · (L [ φ' ]⁻¹)
--   foo ε ψ = ·0< {x = ε} {y = L [ φ' ]⁻¹} ψ φ''

--   buzz : (δ ε : ℚ) → L · ((δ / L [ φ' ]) + (ε / L [ φ' ])) ≡ δ + ε
--   buzz δ ε = L · ((δ / L [ φ' ]) + (ε / L [ φ' ]))
--                ≡⟨ cong (_·_ L) (sym $ ·DistR+ δ ε (L [ φ' ]⁻¹)) ⟩
--              L · ((δ + ε) · L [ φ' ]⁻¹)
--                ≡⟨ cong (_·_ L) (·Comm (δ + ε) (L [ φ' ]⁻¹)) ⟩
--              L · (L [ φ' ]⁻¹ · (δ + ε))
--                ≡⟨ ·Assoc L (L [ φ' ]⁻¹) (δ + ε) ⟩
--              (L · L [ φ' ]⁻¹) · (δ + ε)
--                 ≡⟨ cong (flip _·_ (δ + ε)) (⁻¹-inverse L φ') ⟩
--              1 · (δ + ε)
--                ≡⟨ ·IdL (δ + ε) ⟩
--              δ + ε ∎

--   foo₁ : ((ε : ℚ) → 0 < ε → ℝ) → ((ε : ℚ) → 0 < ε → ℝ)
--   foo₁ g = (λ ε θ → g (ε / L [ φ' ]) (foo ε θ))

--   foo₂ : (g : (ε : ℚ) → 0 < ε → ℝ) →
--          CauchyApproximation'' ℝ B g → 
--          CauchyApproximation (foo₁ g)
--   foo₂ g ψ =
--       (λ δ ε θ ω →
--         -- TODO: Prolly do that crazy sigma trick again
--         let fuz = ψ (δ / L [ φ' ]) (ε / L [ φ' ]) (foo δ θ) (foo ε ω)
--             buz : Σ (0 < δ + ε)
--                     (λ χ → Close (δ + ε)
--                                  χ
--                                  (g (δ / L [ φ' ]) (foo δ θ))
--                                  (g (ε / L [ φ' ]) (foo ε ω)))
--             buz = subst (λ ?x → Σ (0 < ?x)
--                                   (λ χ → Close ?x
--                                                χ
--                                                (g (δ / L [ φ' ]) (foo δ θ))
--                                                (g (ε / L [ φ' ]) (foo ε ω))))
--                         (buzz δ ε)
--                         (·0< {x = L} {y = (δ / L [ φ' ]) + (ε / L [ φ' ])}
--                              φ (+0< {x = δ / L [ φ' ]} {y = ε / L [ φ' ]}
--                                     (foo δ θ)
--                                     (foo ε ω)) ,
--                          fuz)

--             buz' : Close (δ + ε)
--                          (+0< {x = δ} {y = ε} θ ω)
--                          (g (δ / L [ φ' ]) (foo δ θ))
--                          (g (ε / L [ φ' ]) (foo ε ω))
--             buz' = subst (λ ?x → Close (δ + ε)
--                                  ?x
--                                  (g (δ / L [ φ' ]) (foo δ θ))
--                                  (g (ε / L [ φ' ]) (foo ε ω)))
--                          (isProp< 0 (δ + ε) _ _)
--                          (snd buz)
--         in buz')
--     where
--     light : (δ ε : ℚ) →
--             0 < δ → 0 < ε →
--             0 < L · ((δ / L [ φ' ]) + (ε / L [ φ' ]))
--     light δ ε θ ω = subst (_<_ 0) (sym (buzz δ ε)) (+0< {x = δ} {y = ε} θ ω) 

--   liftLipschitzLimit :
--     (f' : (ε : ℚ) → 0 < ε → ℝ) →
--     CauchyApproximation'' ℝ B f' →
--     ℝ
--   liftLipschitzLimit f' ψ =
--     limit
--       (foo₁ f')
--       (foo₂ f' ψ)

--   ψ : (u v : ℝ) → ((ε : ℚ) (φ : 0 < ε) → B u v ε φ) → u ≡ v
--   ψ u v θ = path u v (λ ε ω →
--                        let 
--                        miller : Σ (0 < ε) (λ χ → Close ε χ u v)
--                        miller = subst (λ ?x → Σ (0 < ?x) (λ χ → Close ?x χ u v))
--                                       (·/ ε L φ')
--                                       (·0< {x = L} {y = ε / L [ φ' ]} φ (foo ε ω) , θ (ε / L [ φ' ]) (foo ε ω))

--                        miller' : Close ε ω u v
--                        miller' = subst (λ ?x → Close ε ?x u v) (isProp< 0 ε _ _) (snd miller)
--                        in miller')

--   θ : (q r ε : ℚ) (ω : 0 < ε) →
--       (- ε) < (q - r) →
--       (q - r) < ε →
--       B (liftLipschitzRational q) (liftLipschitzRational r) ε ω
--   θ q r ε ω χ π = george q r ε ω (lemma q r ε π χ)
--     where
--     -- TODO
--     lemma : (q r ε : ℚ) →
--             q - r < ε → - ε < q - r
--             → ∣ q - r ∣ < ε
--     lemma = {!!}

--   -- TODO: Rename f to f'
--   ω : (q ε δ : ℚ) (χ : 0 < ε) (π : 0 < δ) (ρ : 0 < ε - δ)
--       (f : (ε : ℚ) → 0 < ε → ℝ) (σ : CauchyApproximation'' ℝ B f) →
--       B (liftLipschitzRational q) (f δ π) (ε - δ) ρ →
--       B (liftLipschitzRational q) (liftLipschitzLimit f σ) ε χ
--   ω q ε δ χ π ρ f σ τ =
--     closeLimit' (liftLipschitzRational q)
--                 (foo₁ f) (foo₂ f σ)
--                 (L · ε) (L · δ)
--                 (·0< {x = L} {y = ε} φ χ) (·0< {x = L} {y = δ} φ π)
--                 (fst bar₁) (snd bar₁)
--     where
--     -- TODO: Move to lemma
--     bar₀ : L · (ε - δ) ≡ (L · ε) - (L · δ)
--     bar₀ = {!!}

--     bar₃ : f δ π ≡ f ((L · δ) / L [ φ' ]) (foo (L · δ) (·0< {x = L} {y = δ} φ π))
--     bar₃ = cong₂ f (sym (·/' L δ φ')) (isProp→PathP (λ i → isProp< 0 (·/' L δ φ' (~ i))) π (foo (L · δ) (·0< {x = L} {y = δ} φ π))) 

--     bar₂ : Close (L · (ε - δ)) (·0< {x = L} {y = ε - δ} φ ρ)
--                  (liftLipschitzRational q)
--                  (f ((L · δ) / L [ φ' ]) (foo (L · δ) (·0< {x = L} {y = δ} φ π)))
--     bar₂ = subst (λ ?x → Close _ _ _ ?x) bar₃ τ
--       -- Close (L · (ε - (δ + η))) (·0< {x = L} {y = ε - (δ + η)} φ γ)
--       --       (f ((L · δ) / L [ φ' ]) (foo (L · δ) (·0< {x = L} {y = δ} φ α)))
--       --       (g ((L · η) / L [ φ' ]) (foo (L · η) (·0< {x = L} {y = η} φ β)))

--     bar₁ : Σ (0 < (L · ε) - (L · δ))
--              (λ υ → Close ((L · ε) - (L · δ)) υ
--                           (liftLipschitzRational q)
--                           (foo₁ f (L · δ) (·0< {x = L} {y = δ} φ π)))
--     bar₁ = subst (λ ?x → Σ (0 < ?x) (λ υ → Close ?x υ _ _)) bar₀ (·0< {x = L} {y = ε - δ} φ ρ , bar₂) 

--   χ : (f' : (ε : ℚ) → 0 < ε → ℝ) (π : CauchyApproximation'' ℝ B f')
--       (r ε δ : ℚ) (ψ₁ : 0 < ε) (θ₁ : 0 < δ) (ω₁ : 0 < (ε - δ)) →
--       B (f₁ δ θ₁) (liftLipschitzRational r) (ε - δ) ω₁ →
--       B (liftLipschitzLimit f' φ₁) (liftLipschitzRational r) ε ψ₁
--   χ = {!!}

--   π : (f g : (ε : ℚ) → 0 < ε → ℝ)
--       (ρ : CauchyApproximation'' ℝ B f)
--       (τ : CauchyApproximation'' ℝ B g)
--       (ε δ η : ℚ)
--       (υ : 0 < ε) (α : 0 < δ) (β : 0 < η) (γ : 0 < (ε - (δ + η))) →
--       B (f δ α) (g η β) (ε - (δ + η)) γ →
--       B (liftLipschitzLimit f ρ) (liftLipschitzLimit g τ) ε υ
--   π f g ρ τ ε δ η υ α β γ ζ =
--     limitLimit (foo₁ f) (foo₁ g)
--                (foo₂ f ρ) (foo₂ g τ)
--                (L · ε) (L · δ) (L · η)
--                (·0< {x = L} {y = ε} φ υ)
--                (·0< {x = L} {y = δ} φ α)
--                (·0< {x = L} {y = η} φ β)
--                (fst foo₃)
--                (snd foo₃)
--     where
--     foo₅ : L · (ε - (δ + η)) ≡ (L · ε) - (L · δ + L · η)
--     foo₅ = {!!}

--     foo₇ : (f δ α) ≡
--            (f ((L · δ) / L [ φ' ]) (foo (L · δ) (·0< {x = L} {y = δ} φ α)))
--     foo₇ = cong₂ f (sym (·/' L δ φ'))
--                    -- What on God's green earth is (∼ i)
--                    (isProp→PathP (λ i → isProp< 0 (·/' L δ φ' (~ i)))
--                                  α
--                                  (foo (L · δ) (·0< {x = L} {y = δ} φ α)))
--       -- (isProp→PathP (λ i → isProp< 0 δ) α {!foo (L · δ) (·0< {x = L} {y = δ} φ α)!})

--     foo₈ : (g η β) ≡
--            (g ((L · η) / L [ φ' ]) (foo (L · η) (·0< {x = L} {y = η} φ β)))
--     foo₈ = cong₂ g (sym (·/' L η φ'))
--                    (isProp→PathP (λ i → isProp< 0 (·/' L η φ' (~ i)))
--                                  β
--                                  (foo (L · η) (·0< {x = L} {y = η} φ β))) 

--     foo₆ :
--       Close (L · (ε - (δ + η))) (·0< {x = L} {y = ε - (δ + η)} φ γ)
--             (f ((L · δ) / L [ φ' ]) (foo (L · δ) (·0< {x = L} {y = δ} φ α)))
--             (g ((L · η) / L [ φ' ]) (foo (L · η) (·0< {x = L} {y = η} φ β)))
--     foo₆ = subst2 (Close _ _) foo₇ foo₈ ζ

--     foo₃ : Σ (0 < (L · ε) - (L · δ + L · η))
--              (λ foo₄ →
--              Close ((L · ε) - (L · δ + L · η))
--                    foo₄
--                    (foo₁ f (L · δ) (·0< {x = L} {y = δ} φ α))
--                    (foo₁ g (L · η) (·0< {x = L} {y = η} φ β)))
--     foo₃ = subst (λ ?x → Σ (0 < ?x) (λ foo₄ → Close ?x foo₄ _ _))
--                  foo₅
--                  (·0< {x = L} {y = ε - (δ + η)} φ γ , foo₆)

--   ρ : (u v : ℝ) (ε : ℚ) (σ : 0 < ε) → isProp (B u v ε σ)
--   ρ u v ε σ = squash u v (L · ε) (·0< {x = L} {y = ε} φ σ)
