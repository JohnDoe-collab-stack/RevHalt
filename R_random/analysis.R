# ==============================================================================
# Analysis Script
# ==============================================================================

# Load dependencies
source("utils.R")

# ------------------------------------------------------------------------------
# Data Analysis Functions
# ------------------------------------------------------------------------------

#' Perform basic exploratory analysis
#' 
#' @param data A data.frame with numeric columns
#' @return Invisible NULL, prints analysis to console
explore_data <- function(data) {
  cat("\n=== Exploratory Data Analysis ===\n\n")
  
  # Structure
  cat("Structure:\n")
  str(data)
  
  # Summary
  cat("\nSummary:\n")
  print(summary(data))
  
  invisible(NULL)
}

#' Simple visualization (requires ggplot2)
#' 
#' @param data A data.frame with 'value' column
#' @return A ggplot object or NULL if ggplot2 not available
plot_histogram <- function(data) {
  if (!requireNamespace("ggplot2", quietly = TRUE)) {
    message("ggplot2 not installed. Using base R histogram.")
    hist(data$value, main = "Distribution of Values", xlab = "Value")
    return(invisible(NULL))
  }
  
  ggplot2::ggplot(data, ggplot2::aes(x = value)) +
    ggplot2::geom_histogram(bins = 30, fill = "steelblue", color = "white") +
    ggplot2::labs(
      title = "Distribution of Values",
      x = "Value",
      y = "Count"
    ) +
    ggplot2::theme_minimal()
}

# ------------------------------------------------------------------------------
# Example Usage
# ------------------------------------------------------------------------------

if (interactive()) {
  # Generate sample data
  set.seed(123)
  sample_data <- generate_random_data(500, mean = 10, sd = 3)
  
  # Explore
  explore_data(sample_data)
  
  # Visualize
  plot_histogram(sample_data)
}
